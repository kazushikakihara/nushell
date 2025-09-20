use crate::{
    BlockId, DeclId, DeprecationEntry, Example, FromValue, IntoValue, PipelineData, ShellError,
    Span, SyntaxShape, Type, Value, VarId,
    engine::{Call, Command, CommandType, EngineState, Stack},
};
use nu_derive_value::FromValue as DeriveFromValue;
use nu_utils::NuCow;
use serde::{Deserialize, Serialize};
use std::fmt::Write;

// Make nu_protocol available in this namespace, consumers of this crate will
// have this without such an export.
// The `FromValue` derive macro fully qualifies paths to "nu_protocol".
use crate as nu_protocol;

pub enum Parameter {
    Required(PositionalArg),
    Optional(PositionalArg),
    Rest(PositionalArg),
    Flag(Flag),
}

impl From<Flag> for Parameter {
    fn from(value: Flag) -> Self {
        Self::Flag(value)
    }
}

/// The signature definition of a named flag that either accepts a value or acts as a toggle flag
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct Flag {
    pub long: String,
    pub short: Option<char>,
    pub arg: Option<SyntaxShape>,
    pub required: bool,
    pub desc: String,
    pub completion: Option<Completion>,

    // For custom commands
    pub var_id: Option<VarId>,
    pub default_value: Option<Value>,
    #[serde(default)]
    pub parameter_sets: Vec<String>,
    #[serde(default)]
    pub parameter_set_mandatory: Vec<String>,
}

impl Flag {
    #[inline]
    pub fn new(long: impl Into<String>) -> Self {
        Flag {
            long: long.into(),
            short: None,
            arg: None,
            required: false,
            desc: String::new(),
            completion: None,
            var_id: None,
            default_value: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        }
    }

    #[inline]
    pub fn short(self, short: char) -> Self {
        Self {
            short: Some(short),
            ..self
        }
    }

    #[inline]
    pub fn arg(self, arg: SyntaxShape) -> Self {
        Self {
            arg: Some(arg),
            ..self
        }
    }

    #[inline]
    pub fn required(self) -> Self {
        Self {
            required: true,
            ..self
        }
    }

    #[inline]
    pub fn desc(self, desc: impl Into<String>) -> Self {
        Self {
            desc: desc.into(),
            ..self
        }
    }

    #[inline]
    pub fn completion(self, completion: Completion) -> Self {
        Self {
            completion: Some(completion),
            ..self
        }
    }
}

/// The signature definition for a positional argument
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct PositionalArg {
    pub name: String,
    pub desc: String,
    pub shape: SyntaxShape,
    pub completion: Option<Completion>,

    // For custom commands
    pub var_id: Option<VarId>,
    pub default_value: Option<Value>,
    #[serde(default)]
    pub parameter_sets: Vec<String>,
    #[serde(default)]
    pub parameter_set_mandatory: Vec<String>,
}

impl PositionalArg {
    #[inline]
    pub fn new(name: impl Into<String>, shape: SyntaxShape) -> Self {
        Self {
            name: name.into(),
            desc: String::new(),
            shape,
            completion: None,
            var_id: None,
            default_value: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        }
    }

    #[inline]
    pub fn desc(self, desc: impl Into<String>) -> Self {
        Self {
            desc: desc.into(),
            ..self
        }
    }

    #[inline]
    pub fn completion(self, completion: Completion) -> Self {
        Self {
            completion: Some(completion),
            ..self
        }
    }

    #[inline]
    pub fn required(self) -> Parameter {
        Parameter::Required(self)
    }

    #[inline]
    pub fn optional(self) -> Parameter {
        Parameter::Optional(self)
    }

    #[inline]
    pub fn rest(self) -> Parameter {
        Parameter::Rest(self)
    }
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub enum Completion {
    Command(DeclId),
    List(NuCow<&'static [&'static str], Vec<String>>),
}

impl Completion {
    pub const fn new_list(list: &'static [&'static str]) -> Self {
        Self::List(NuCow::Borrowed(list))
    }

    pub fn to_value(&self, engine_state: &EngineState, span: Span) -> Value {
        match self {
            Completion::Command(id) => engine_state
                .get_decl(*id)
                .name()
                .to_owned()
                .into_value(span),
            Completion::List(list) => match list {
                NuCow::Borrowed(list) => list
                    .iter()
                    .map(|&e| e.into_value(span))
                    .collect::<Vec<Value>>()
                    .into_value(span),
                NuCow::Owned(list) => list
                    .iter()
                    .cloned()
                    .map(|e| e.into_value(span))
                    .collect::<Vec<Value>>()
                    .into_value(span),
            },
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ParameterSet {
    pub name: String,
}

impl ParameterSet {
    #[inline]
    pub fn new(name: impl Into<String>) -> Self {
        Self { name: name.into() }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ParameterId {
    Positional(usize),
    Rest,
    Flag(String),
}

#[derive(Debug, Clone)]
pub enum ParameterRole {
    RequiredPositional,
    OptionalPositional,
    Rest,
    Flag {
        long: Option<String>,
        short: Option<char>,
    },
}

#[derive(Debug, Clone)]
pub struct ParameterMembership {
    pub all_sets: bool,
    pub sets: Vec<String>,
}

impl ParameterMembership {
    pub fn new(sets: Vec<String>) -> Self {
        Self {
            all_sets: sets.is_empty(),
            sets,
        }
    }

    pub fn active_sets<'a>(&'a self, all_sets: &'a [String]) -> Vec<&'a str> {
        if self.all_sets {
            all_sets.iter().map(|s| s.as_str()).collect()
        } else {
            self.sets.iter().map(|s| s.as_str()).collect()
        }
    }
}

#[derive(Debug, Clone)]
pub struct ParameterMetadata {
    pub id: ParameterId,
    pub name: String,
    pub display_name: String,
    pub role: ParameterRole,
    pub membership: ParameterMembership,
    pub mandatory_sets: Vec<String>,
}

impl ParameterMetadata {
    fn from_positional(
        id: ParameterId,
        arg: &PositionalArg,
        role: ParameterRole,
        set_names: &[String],
    ) -> Self {
        let mut membership = ParameterMembership::new(arg.parameter_sets.clone());
        let mut mandatory_sets = arg.parameter_set_mandatory.clone();
        Self::expand_mandatory(&mut membership, &mut mandatory_sets, set_names);

        let display_name = match role {
            ParameterRole::Rest => format!("...{}", arg.name),
            ParameterRole::OptionalPositional => format!("({})", arg.name),
            ParameterRole::RequiredPositional => format!("<{}>", arg.name),
            ParameterRole::Flag { .. } => {
                unreachable!("flags should not use positional constructor")
            }
        };

        Self {
            id,
            name: arg.name.clone(),
            display_name,
            role,
            membership,
            mandatory_sets,
        }
    }

    fn from_flag(flag: &Flag, set_names: &[String]) -> Self {
        let mut membership = ParameterMembership::new(flag.parameter_sets.clone());
        let mut mandatory_sets = flag.parameter_set_mandatory.clone();
        Self::expand_mandatory(&mut membership, &mut mandatory_sets, set_names);

        let long = if flag.long.is_empty() {
            None
        } else {
            Some(flag.long.clone())
        };
        let short = flag.short;
        let display_name = match (&long, short) {
            (Some(long), Some(short)) => format!("--{long} (-{short})"),
            (Some(long), None) => format!("--{long}"),
            (None, Some(short)) => format!("-{short}"),
            (None, None) => "--".to_string(),
        };

        let id = ParameterId::Flag(flag_key(&flag.long, flag.short));
        let name = long.clone().unwrap_or_else(|| {
            short
                .map(|c| c.to_string())
                .unwrap_or_else(|| "flag".to_string())
        });

        Self {
            id,
            name,
            display_name,
            role: ParameterRole::Flag { long, short },
            membership,
            mandatory_sets,
        }
    }

    fn expand_mandatory(
        membership: &mut ParameterMembership,
        mandatory_sets: &mut Vec<String>,
        all_sets: &[String],
    ) {
        dedup_strings(mandatory_sets);

        if membership.all_sets {
            // Parameters that belong to all parameter sets are only mandatory in
            // those sets if they were explicitly marked as such via
            // `@mandatory` or `@mandatory(...)`.
            mandatory_sets.retain(|set| all_sets.iter().any(|name| name == set));
        } else if !membership.sets.is_empty() {
            mandatory_sets.retain(|set| membership.sets.iter().any(|m| m == set));
        }
    }

    pub fn membership_sets<'a>(&'a self, all_sets: &'a [String]) -> Vec<&'a str> {
        self.membership.active_sets(all_sets)
    }

    pub fn belongs_to_set(&self, set: &str, all_sets: &[String]) -> bool {
        self.membership_sets(all_sets).contains(&set)
    }

    pub fn is_mandatory_in(&self, set: &str) -> bool {
        self.mandatory_sets.iter().any(|s| s == set)
    }
}

#[derive(Debug, Clone)]
pub struct ParameterSetsMetadata {
    pub set_names: Vec<String>,
    pub parameters: Vec<ParameterMetadata>,
}

impl ParameterSetsMetadata {
    pub fn is_empty(&self) -> bool {
        self.set_names.is_empty()
    }

    pub fn summaries(&self) -> Vec<String> {
        self.set_names
            .iter()
            .map(|set| {
                let parts: Vec<String> = self
                    .parameters
                    .iter()
                    .filter(|param| param.belongs_to_set(set, &self.set_names))
                    .map(|param| {
                        let mut text = param.display_name.clone();
                        if param.is_mandatory_in(set) {
                            text.push_str(" (mandatory)");
                        }
                        text
                    })
                    .collect();

                if parts.is_empty() {
                    format!("{set}: no arguments")
                } else {
                    format!("{set}: {}", parts.join(", "))
                }
            })
            .collect()
    }
}

fn flag_key(long: &str, short: Option<char>) -> String {
    if !long.is_empty() {
        long.to_string()
    } else if let Some(short) = short {
        format!("(short {short})")
    } else {
        "flag".to_string()
    }
}

fn dedup_strings(values: &mut Vec<String>) {
    let mut i = 0;
    while i < values.len() {
        let mut j = i + 1;
        while j < values.len() {
            if values[j] == values[i] {
                values.remove(j);
            } else {
                j += 1;
            }
        }
        i += 1;
    }
}

/// Command categories
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum Category {
    Bits,
    Bytes,
    Chart,
    Conversions,
    Core,
    Custom(String),
    Database,
    Date,
    Debug,
    Default,
    Deprecated,
    Removed,
    Env,
    Experimental,
    FileSystem,
    Filters,
    Formats,
    Generators,
    Hash,
    History,
    Math,
    Misc,
    Network,
    Path,
    Platform,
    Plugin,
    Random,
    Shells,
    Strings,
    System,
    Viewers,
}

impl std::fmt::Display for Category {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let msg = match self {
            Category::Bits => "bits",
            Category::Bytes => "bytes",
            Category::Chart => "chart",
            Category::Conversions => "conversions",
            Category::Core => "core",
            Category::Custom(name) => name,
            Category::Database => "database",
            Category::Date => "date",
            Category::Debug => "debug",
            Category::Default => "default",
            Category::Deprecated => "deprecated",
            Category::Removed => "removed",
            Category::Env => "env",
            Category::Experimental => "experimental",
            Category::FileSystem => "filesystem",
            Category::Filters => "filters",
            Category::Formats => "formats",
            Category::Generators => "generators",
            Category::Hash => "hash",
            Category::History => "history",
            Category::Math => "math",
            Category::Misc => "misc",
            Category::Network => "network",
            Category::Path => "path",
            Category::Platform => "platform",
            Category::Plugin => "plugin",
            Category::Random => "random",
            Category::Shells => "shells",
            Category::Strings => "strings",
            Category::System => "system",
            Category::Viewers => "viewers",
        };

        write!(f, "{msg}")
    }
}

pub fn category_from_string(category: &str) -> Category {
    match category {
        "bits" => Category::Bits,
        "bytes" => Category::Bytes,
        "chart" => Category::Chart,
        "conversions" => Category::Conversions,
        // Let's protect our own "core" commands by preventing scripts from having this category.
        "core" => Category::Custom("custom_core".to_string()),
        "database" => Category::Database,
        "date" => Category::Date,
        "debug" => Category::Debug,
        "default" => Category::Default,
        "deprecated" => Category::Deprecated,
        "removed" => Category::Removed,
        "env" => Category::Env,
        "experimental" => Category::Experimental,
        "filesystem" => Category::FileSystem,
        "filter" => Category::Filters,
        "formats" => Category::Formats,
        "generators" => Category::Generators,
        "hash" => Category::Hash,
        "history" => Category::History,
        "math" => Category::Math,
        "misc" => Category::Misc,
        "network" => Category::Network,
        "path" => Category::Path,
        "platform" => Category::Platform,
        "plugin" => Category::Plugin,
        "random" => Category::Random,
        "shells" => Category::Shells,
        "strings" => Category::Strings,
        "system" => Category::System,
        "viewers" => Category::Viewers,
        _ => Category::Custom(category.to_string()),
    }
}

/// Signature information of a [`Command`]
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct Signature {
    pub name: String,
    pub description: String,
    pub extra_description: String,
    pub search_terms: Vec<String>,
    pub required_positional: Vec<PositionalArg>,
    pub optional_positional: Vec<PositionalArg>,
    pub rest_positional: Option<PositionalArg>,
    pub named: Vec<Flag>,
    #[serde(default)]
    pub parameter_sets: Vec<ParameterSet>,
    pub input_output_types: Vec<(Type, Type)>,
    pub allow_variants_without_examples: bool,
    pub is_filter: bool,
    pub creates_scope: bool,
    pub allows_unknown_args: bool,
    // Signature category used to classify commands stored in the list of declarations
    pub category: Category,
}

impl PartialEq for Signature {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
            && self.description == other.description
            && self.required_positional == other.required_positional
            && self.optional_positional == other.optional_positional
            && self.rest_positional == other.rest_positional
            && self.is_filter == other.is_filter
    }
}

impl Eq for Signature {}

impl Signature {
    /// Creates a new signature for a command with `name`
    pub fn new(name: impl Into<String>) -> Signature {
        Signature {
            name: name.into(),
            description: String::new(),
            extra_description: String::new(),
            search_terms: vec![],
            required_positional: vec![],
            optional_positional: vec![],
            rest_positional: None,
            input_output_types: vec![],
            allow_variants_without_examples: false,
            named: vec![],
            parameter_sets: vec![],
            is_filter: false,
            creates_scope: false,
            category: Category::Default,
            allows_unknown_args: false,
        }
    }

    /// Gets the input type from the signature
    ///
    /// If the input was unspecified or the signature has several different
    /// input types, [`Type::Any`] is returned.  Otherwise, if the signature has
    /// one or same input types, this type is returned.
    // XXX: remove?
    pub fn get_input_type(&self) -> Type {
        match self.input_output_types.len() {
            0 => Type::Any,
            1 => self.input_output_types[0].0.clone(),
            _ => {
                let first = &self.input_output_types[0].0;
                if self
                    .input_output_types
                    .iter()
                    .all(|(input, _)| input == first)
                {
                    first.clone()
                } else {
                    Type::Any
                }
            }
        }
    }

    /// Gets the output type from the signature
    ///
    /// If the output was unspecified or the signature has several different
    /// input types, [`Type::Any`] is returned.  Otherwise, if the signature has
    /// one or same output types, this type is returned.
    // XXX: remove?
    pub fn get_output_type(&self) -> Type {
        match self.input_output_types.len() {
            0 => Type::Any,
            1 => self.input_output_types[0].1.clone(),
            _ => {
                let first = &self.input_output_types[0].1;
                if self
                    .input_output_types
                    .iter()
                    .all(|(_, output)| output == first)
                {
                    first.clone()
                } else {
                    Type::Any
                }
            }
        }
    }

    /// Add a default help option to a signature
    pub fn add_help(mut self) -> Signature {
        // default help flag
        let flag = Flag {
            long: "help".into(),
            short: Some('h'),
            arg: None,
            desc: "Display the help message for this command".into(),
            required: false,
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        };
        self.named.push(flag);
        self
    }

    /// Build an internal signature with default help option
    ///
    /// This is equivalent to `Signature::new(name).add_help()`.
    pub fn build(name: impl Into<String>) -> Signature {
        Signature::new(name.into()).add_help()
    }

    /// Add a description to the signature
    ///
    /// This should be a single sentence as it is the part shown for example in the completion
    /// menu.
    pub fn description(mut self, msg: impl Into<String>) -> Signature {
        self.description = msg.into();
        self
    }

    /// Add an extra description to the signature.
    ///
    /// Here additional documentation can be added
    pub fn extra_description(mut self, msg: impl Into<String>) -> Signature {
        self.extra_description = msg.into();
        self
    }

    /// Add search terms to the signature
    pub fn search_terms(mut self, terms: Vec<String>) -> Signature {
        self.search_terms = terms;
        self
    }

    /// Update signature's fields from a Command trait implementation
    pub fn update_from_command(mut self, command: &dyn Command) -> Signature {
        self.search_terms = command
            .search_terms()
            .into_iter()
            .map(|term| term.to_string())
            .collect();
        self.extra_description = command.extra_description().to_string();
        self.description = command.description().to_string();
        self
    }

    /// Allow unknown signature parameters
    pub fn allows_unknown_args(mut self) -> Signature {
        self.allows_unknown_args = true;
        self
    }

    pub fn param(mut self, param: impl Into<Parameter>) -> Self {
        let param: Parameter = param.into();
        match param {
            Parameter::Flag(flag) => {
                if let Some(s) = flag.short {
                    assert!(
                        !self.get_shorts().contains(&s),
                        "There may be duplicate short flags for '-{s}'"
                    );
                }

                let name = flag.long.as_str();
                assert!(
                    !self.get_names().contains(&name),
                    "There may be duplicate name flags for '--{name}'"
                );

                self.named.push(flag);
            }
            Parameter::Required(positional_arg) => {
                self.required_positional.push(positional_arg);
            }
            Parameter::Optional(positional_arg) => {
                self.optional_positional.push(positional_arg);
            }
            Parameter::Rest(positional_arg) => {
                assert!(
                    self.rest_positional.is_none(),
                    "Tried to set rest arguments more than once"
                );
                self.rest_positional = Some(positional_arg);
            }
        }
        self
    }

    /// Add a required positional argument to the signature
    pub fn required(
        mut self,
        name: impl Into<String>,
        shape: impl Into<SyntaxShape>,
        desc: impl Into<String>,
    ) -> Signature {
        self.required_positional.push(PositionalArg {
            name: name.into(),
            desc: desc.into(),
            shape: shape.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Add an optional positional argument to the signature
    pub fn optional(
        mut self,
        name: impl Into<String>,
        shape: impl Into<SyntaxShape>,
        desc: impl Into<String>,
    ) -> Signature {
        self.optional_positional.push(PositionalArg {
            name: name.into(),
            desc: desc.into(),
            shape: shape.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Add a rest positional parameter
    ///
    /// Rest positionals (also called [rest parameters][rp]) are treated as
    /// optional: passing 0 arguments is a valid call.  If the command requires
    /// at least one argument, it must be checked by the implementation.
    ///
    /// [rp]: https://www.nushell.sh/book/custom_commands.html#rest-parameters
    pub fn rest(
        mut self,
        name: &str,
        shape: impl Into<SyntaxShape>,
        desc: impl Into<String>,
    ) -> Signature {
        self.rest_positional = Some(PositionalArg {
            name: name.into(),
            desc: desc.into(),
            shape: shape.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Is this command capable of operating on its input via cell paths?
    pub fn operates_on_cell_paths(&self) -> bool {
        self.required_positional
            .iter()
            .chain(self.rest_positional.iter())
            .any(|pos| {
                matches!(
                    pos,
                    PositionalArg {
                        shape: SyntaxShape::CellPath,
                        ..
                    }
                )
            })
    }

    /// Add an optional named flag argument to the signature
    pub fn named(
        mut self,
        name: impl Into<String>,
        shape: impl Into<SyntaxShape>,
        desc: impl Into<String>,
        short: Option<char>,
    ) -> Signature {
        let (name, s) = self.check_names(name, short);

        self.named.push(Flag {
            long: name,
            short: s,
            arg: Some(shape.into()),
            required: false,
            desc: desc.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Add a required named flag argument to the signature
    pub fn required_named(
        mut self,
        name: impl Into<String>,
        shape: impl Into<SyntaxShape>,
        desc: impl Into<String>,
        short: Option<char>,
    ) -> Signature {
        let (name, s) = self.check_names(name, short);

        self.named.push(Flag {
            long: name,
            short: s,
            arg: Some(shape.into()),
            required: true,
            desc: desc.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Add a switch to the signature
    pub fn switch(
        mut self,
        name: impl Into<String>,
        desc: impl Into<String>,
        short: Option<char>,
    ) -> Signature {
        let (name, s) = self.check_names(name, short);

        self.named.push(Flag {
            long: name,
            short: s,
            arg: None,
            required: false,
            desc: desc.into(),
            var_id: None,
            default_value: None,
            completion: None,
            parameter_sets: vec![],
            parameter_set_mandatory: vec![],
        });

        self
    }

    /// Changes the input type of the command signature
    pub fn input_output_type(mut self, input_type: Type, output_type: Type) -> Signature {
        self.input_output_types.push((input_type, output_type));
        self
    }

    /// Set the input-output type signature variants of the command
    pub fn input_output_types(mut self, input_output_types: Vec<(Type, Type)>) -> Signature {
        self.input_output_types = input_output_types;
        self
    }

    /// Changes the signature category
    pub fn category(mut self, category: Category) -> Signature {
        self.category = category;

        self
    }

    /// Sets that signature will create a scope as it parses
    pub fn creates_scope(mut self) -> Signature {
        self.creates_scope = true;
        self
    }

    // Is it allowed for the type signature to feature a variant that has no corresponding example?
    pub fn allow_variants_without_examples(mut self, allow: bool) -> Signature {
        self.allow_variants_without_examples = allow;
        self
    }

    /// A string rendering of the command signature
    ///
    /// If the command has flags, all of them will be shown together as
    /// `{flags}`.
    pub fn call_signature(&self) -> String {
        let mut one_liner = String::new();
        one_liner.push_str(&self.name);
        one_liner.push(' ');

        // Note: the call signature needs flags first because on the nu commandline,
        // flags will precede the script file name. Flags for internal commands can come
        // either before or after (or around) positional parameters, so there isn't a strong
        // preference, so we default to the more constrained example.
        if self.named.len() > 1 {
            one_liner.push_str("{flags} ");
        }

        for positional in &self.required_positional {
            one_liner.push_str(&get_positional_short_name(positional, true));
        }
        for positional in &self.optional_positional {
            one_liner.push_str(&get_positional_short_name(positional, false));
        }

        if let Some(rest) = &self.rest_positional {
            let _ = write!(one_liner, "...{}", get_positional_short_name(rest, false));
        }

        // if !self.subcommands.is_empty() {
        //     one_liner.push_str("<subcommand> ");
        // }

        one_liner
    }

    /// Get list of the short-hand flags
    pub fn get_shorts(&self) -> Vec<char> {
        self.named.iter().filter_map(|f| f.short).collect()
    }

    /// Get list of the long-hand flags
    pub fn get_names(&self) -> Vec<&str> {
        self.named.iter().map(|f| f.long.as_str()).collect()
    }

    /// Checks if short or long options are already present
    ///
    /// ## Panics
    ///
    /// Panics if one of them is found.
    // XXX: return result instead of a panic
    fn check_names(&self, name: impl Into<String>, short: Option<char>) -> (String, Option<char>) {
        let s = short.inspect(|c| {
            assert!(
                !self.get_shorts().contains(c),
                "There may be duplicate short flags for '-{c}'"
            );
        });

        let name = {
            let name: String = name.into();
            assert!(
                !self.get_names().contains(&name.as_str()),
                "There may be duplicate name flags for '--{name}'"
            );
            name
        };

        (name, s)
    }

    /// Returns an argument with the index `position`
    ///
    /// It will index, in order, required arguments, then optional, then the
    /// trailing `...rest` argument.
    pub fn get_positional(&self, position: usize) -> Option<&PositionalArg> {
        if position < self.required_positional.len() {
            self.required_positional.get(position)
        } else if position < (self.required_positional.len() + self.optional_positional.len()) {
            self.optional_positional
                .get(position - self.required_positional.len())
        } else {
            self.rest_positional.as_ref()
        }
    }

    /// Returns the number of (optional) positional parameters in a signature
    ///
    /// This does _not_ include the `...rest` parameter, even if it's present.
    pub fn num_positionals(&self) -> usize {
        let mut total = self.required_positional.len() + self.optional_positional.len();

        for positional in &self.required_positional {
            if let SyntaxShape::Keyword(..) = positional.shape {
                // Keywords have a required argument, so account for that
                total += 1;
            }
        }
        for positional in &self.optional_positional {
            if let SyntaxShape::Keyword(..) = positional.shape {
                // Keywords have a required argument, so account for that
                total += 1;
            }
        }
        total
    }

    /// Find the matching long flag
    pub fn get_long_flag(&self, name: &str) -> Option<Flag> {
        for flag in &self.named {
            if flag.long == name {
                return Some(flag.clone());
            }
        }
        None
    }

    /// Find the matching long flag
    pub fn get_short_flag(&self, short: char) -> Option<Flag> {
        for flag in &self.named {
            if let Some(short_flag) = &flag.short
                && *short_flag == short
            {
                return Some(flag.clone());
            }
        }
        None
    }

    /// Set the filter flag for the signature
    pub fn filter(mut self) -> Signature {
        self.is_filter = true;
        self
    }

    /// Create a placeholder implementation of Command as a way to predeclare a definition's
    /// signature so other definitions can see it. This placeholder is later replaced with the
    /// full definition in a second pass of the parser.
    pub fn predeclare(self) -> Box<dyn Command> {
        Box::new(Predeclaration { signature: self })
    }

    /// Combines a signature and a block into a runnable block
    pub fn into_block_command(
        self,
        block_id: BlockId,
        attributes: Vec<(String, Value)>,
        examples: Vec<CustomExample>,
    ) -> Box<dyn Command> {
        Box::new(BlockCommand {
            signature: self,
            block_id,
            attributes,
            examples,
        })
    }

    pub fn collect_parameter_sets(&self) -> ParameterSetsMetadata {
        let mut set_names: Vec<String> = Vec::new();

        let mut add_set = |name: &str| {
            if !name.is_empty() && !set_names.iter().any(|existing| existing == name) {
                set_names.push(name.to_string());
            }
        };

        for parameter_set in &self.parameter_sets {
            add_set(&parameter_set.name);
        }

        let mut extend_sets = |sets: &[String]| {
            for name in sets {
                add_set(name);
            }
        };

        for positional in &self.required_positional {
            extend_sets(&positional.parameter_sets);
            extend_sets(&positional.parameter_set_mandatory);
        }

        for positional in &self.optional_positional {
            extend_sets(&positional.parameter_sets);
            extend_sets(&positional.parameter_set_mandatory);
        }

        if let Some(rest) = &self.rest_positional {
            extend_sets(&rest.parameter_sets);
            extend_sets(&rest.parameter_set_mandatory);
        }

        for flag in &self.named {
            extend_sets(&flag.parameter_sets);
            extend_sets(&flag.parameter_set_mandatory);
        }

        let mut parameters = Vec::new();

        for (idx, positional) in self.required_positional.iter().enumerate() {
            parameters.push(ParameterMetadata::from_positional(
                ParameterId::Positional(idx),
                positional,
                ParameterRole::RequiredPositional,
                &set_names,
            ));
        }

        let mut positional_index = self.required_positional.len();
        for positional in &self.optional_positional {
            parameters.push(ParameterMetadata::from_positional(
                ParameterId::Positional(positional_index),
                positional,
                ParameterRole::OptionalPositional,
                &set_names,
            ));
            positional_index += 1;
        }

        if let Some(rest) = &self.rest_positional {
            parameters.push(ParameterMetadata::from_positional(
                ParameterId::Rest,
                rest,
                ParameterRole::Rest,
                &set_names,
            ));
        }

        for flag in &self.named {
            parameters.push(ParameterMetadata::from_flag(flag, &set_names));
        }

        ParameterSetsMetadata {
            set_names,
            parameters,
        }
    }
}

#[derive(Clone)]
struct Predeclaration {
    signature: Signature,
}

impl Command for Predeclaration {
    fn name(&self) -> &str {
        &self.signature.name
    }

    fn signature(&self) -> Signature {
        self.signature.clone()
    }

    fn description(&self) -> &str {
        &self.signature.description
    }

    fn extra_description(&self) -> &str {
        &self.signature.extra_description
    }

    fn run(
        &self,
        _engine_state: &EngineState,
        _stack: &mut Stack,
        _call: &Call,
        _input: PipelineData,
    ) -> Result<PipelineData, crate::ShellError> {
        panic!("Internal error: can't run a predeclaration without a body")
    }
}

fn get_positional_short_name(arg: &PositionalArg, is_required: bool) -> String {
    match &arg.shape {
        SyntaxShape::Keyword(name, ..) => {
            if is_required {
                format!("{} <{}> ", String::from_utf8_lossy(name), arg.name)
            } else {
                format!("({} <{}>) ", String::from_utf8_lossy(name), arg.name)
            }
        }
        _ => {
            if is_required {
                format!("<{}> ", arg.name)
            } else {
                format!("({}) ", arg.name)
            }
        }
    }
}

#[derive(Clone, DeriveFromValue)]
pub struct CustomExample {
    pub example: String,
    pub description: String,
    pub result: Option<Value>,
}

impl CustomExample {
    pub fn to_example(&self) -> Example<'_> {
        Example {
            example: self.example.as_str(),
            description: self.description.as_str(),
            result: self.result.clone(),
        }
    }
}

#[derive(Clone)]
struct BlockCommand {
    signature: Signature,
    block_id: BlockId,
    attributes: Vec<(String, Value)>,
    examples: Vec<CustomExample>,
}

impl Command for BlockCommand {
    fn name(&self) -> &str {
        &self.signature.name
    }

    fn signature(&self) -> Signature {
        self.signature.clone()
    }

    fn description(&self) -> &str {
        &self.signature.description
    }

    fn extra_description(&self) -> &str {
        &self.signature.extra_description
    }

    fn run(
        &self,
        _engine_state: &EngineState,
        _stack: &mut Stack,
        _call: &Call,
        _input: PipelineData,
    ) -> Result<crate::PipelineData, crate::ShellError> {
        Err(ShellError::GenericError {
            error: "Internal error: can't run custom command with 'run', use block_id".into(),
            msg: "".into(),
            span: None,
            help: None,
            inner: vec![],
        })
    }

    fn command_type(&self) -> CommandType {
        CommandType::Custom
    }

    fn block_id(&self) -> Option<BlockId> {
        Some(self.block_id)
    }

    fn attributes(&self) -> Vec<(String, Value)> {
        self.attributes.clone()
    }

    fn examples(&self) -> Vec<Example<'_>> {
        self.examples
            .iter()
            .map(CustomExample::to_example)
            .collect()
    }

    fn search_terms(&self) -> Vec<&str> {
        self.signature
            .search_terms
            .iter()
            .map(String::as_str)
            .collect()
    }

    fn deprecation_info(&self) -> Vec<DeprecationEntry> {
        self.attributes
            .iter()
            .filter_map(|(key, value)| {
                (key == "deprecated")
                    .then_some(value.clone())
                    .map(DeprecationEntry::from_value)
                    .and_then(Result::ok)
            })
            .collect()
    }
}
