from intbase import InterpreterBase, ErrorType
from brewparse import parse_program
import enum
import copy


class Type(enum.Enum):
    NIL = 0
    INT = 1
    STRING = 2
    BOOL = 3
    VOID = 4
    OBJECT = 5
    FUNCTION = 6


class Value:
    def __init__(self, t=None, v=None):
        if t is None:
            self.t = Type.NIL
            self.v = None
        else:
            self.t = t
            self.v = v

class Cell:
    def __init__(self, value: Value):
        self.value = value

    def get(self) -> Value:
        return self.value
    
    def set(self, value: Value):
        self.value = value

class FunctionValue:
    def __init__(self, func_ast, param_types: tuple[Type, ...], closure_env=None):
        self.func_ast = func_ast
        self.param_types = tuple(param_types)
        self.closure_env = closure_env


class Environment:
    def __init__(self):
        self.env = []

    def enter_block(self):
        self.env[-1].append({})

    def exit_block(self):
        self.env[-1].pop()

    def enter_func(self):
        self.env.append([{}])

    def exit_func(self):
        self.env.pop()

    # define new variable at function scope
    # def fdef(self, varname):
    #     if self.exists(varname):
    #         return False
    #     top_env = self.env[-1]
    #     top_env[0][varname] = Value()
    #     return True

    def fdef_function(self, varname, initial_value: Value):
        if self.exists_in_function_scope(varname):
            return False
        top_env = self.env[-1]
        # top_env[0][varname] = initial_value
        top_env[0][varname] = Cell(initial_value)
        return True
    
    def fdef_function_cell(self, varname, cell: Cell):
        if self.exists_in_function_scope(varname):
            return False
        top_env = self.env[-1]
        top_env[0][varname] = cell
        return True
    
    def fdef_block(self, varname, initial_value: Value):
        if self.exists_in_current_block(varname):
            return False
        top_env = self.env[-1]
        top_env[-1][varname] = Cell(initial_value)
        # top_env[-1][varname] = initial_value
        return True
    
    def get_current_cell(self, varname):
        # top_env = self.env[-1]
        for frame in reversed(self.env):
            for block in reversed(frame):
                if varname in block:
                    return block[varname]  
        return None

    def exists(self, varname):
        for frame in reversed(self.env):
            for block in reversed(frame):
                if varname in block:
                    return True
        return False
    
    def exists_in_current_block(self, varname):
        return varname in self.env[-1][-1]
    
    def exists_in_function_scope(self, varname):
        return varname in self.env[-1][0]

    def get(self, varname):
        top_env = self.env[-1]
        for block in reversed(top_env):
            if varname in block:
                return block[varname].value
        return None

    def set(self, varname, value):
        # if not self.exists(varname):
        #     return False
        for frame in reversed(self.env):
            for block in reversed(frame):
                if varname in block:
                    block[varname].value = value
                    return True
        return False

class Interpreter(InterpreterBase):
    def __init__(self, console_output=True, inp=None, trace_output=False):
        super().__init__(console_output, inp)
        self.funcs = {}
        self.env = Environment()
        self.bops = {"+", "-", "*", "/", "==", "!=", ">", ">=", "<", "<=", "||", "&&"}
        self.current_return_type = Type.VOID
        self.heap = {}
        self.next_obj_id = 1
        self.current_return_interface = None
        self.interfaces = {}

    def new_object(self) -> Value:
        obj_id = self.next_obj_id
        self.next_obj_id += 1
        self.heap[obj_id] = {}
        return Value(Type.OBJECT, obj_id)
    
    def interface_from_suffix(self, suffix:str):
        if suffix.isupper():
            return suffix
        return None
    
    def compatible_interfaces(self, expected_interface, value_interface, val: Value) -> bool:
        if expected_interface is None:
            return True
        if val.v is None and val.t in (Type.OBJECT, Type.FUNCTION):
            return True
        if value_interface is None:
            return False
        return (expected_interface == value_interface)
    
    def object_satisfies_interface(self, interface_name:str, val:Value) -> bool:
        if interface_name is None:
            return True
        if val.t != Type.OBJECT:
            return False
        if val.v is None:
            return True
        if interface_name not in self.interfaces:
            super().error(ErrorType.NAME_ERROR, "unknown interface in object_satisfies_interface")
        interface = self.interfaces[interface_name]
        object_fields = self.heap.get(val.v)
        if object_fields is None:
            super().error(ErrorType.FAULT_ERROR, "invalid object reference in object_satisfies_interface")
        for fname, spec in interface["fields"].items():
            if fname not in object_fields:
                return False
            field_val = object_fields[fname].get()
            if spec["kind"] == "var":
                if field_val.t != spec["type"]:
                    return False
                finterface = spec["interface"]
                if finterface is not None:
                    if field_val.t != Type.OBJECT:
                        return False
                    if not self.object_satisfies_interface(finterface, field_val):
                        return False
            elif spec["kind"] == "func":
                if field_val.t != Type.FUNCTION or field_val.v is None:
                    return False
                func_def = field_val.v.func_ast
                formal_params = func_def.get("args")
                required_params = spec["params"]
                if len(formal_params) != len(required_params):
                    return False
                for formal, required in zip(formal_params, required_params):
                    actual_type = formal.dict["declared_type"]
                    actual_interface = formal.dict["interface"]
                    actual_ref = formal.get("ref")
                    required_type = required["type"]
                    required_interface = required["interface"]
                    required_ref = required["ref"]
                    if actual_ref != required_ref:
                        return False
                    if required_type == Type.OBJECT and required_interface is None:
                        if actual_type != Type.OBJECT:
                            return False
                    elif required_type == Type.OBJECT and required_interface is not None:
                        if actual_type != Type.OBJECT or actual_interface != required_interface:
                            return False
                    else:
                        if actual_type != required_type or actual_interface != required_interface:
                            return False
            else:
                return False    
        return True
    def interface_from_name(self, name:str):
        suffix = name[-1]
        return self.interface_from_suffix(suffix)
    
    def is_nil_object(self, val:Value)->bool:
        return val.t == Type.OBJECT and val.v is None
    
    def is_nil_value(self, val:Value)->bool:
        return (val.t in (Type.OBJECT, Type.FUNCTION) and val.v is None)
    
    def get_qname_value(self, qname:str) ->Value:
        cell = self.get_qname_cell(qname)
        return cell.get()

    def make_named_function_value(self, name:str) ->Value:
        potential = []
        for (fname, ptypes), func in self.funcs.items():
            if fname == name:
                potential.append(func)

        if len(potential) == 0:
            super().error(ErrorType.NAME_ERROR, "function wasnt found!!!!!!!!!!!!!!!!")
        if len(potential) > 1:
            super().error(ErrorType.NAME_ERROR, "ambiguous function name!!!!!!!!!!!!!!!!")
        # if not potential:
        #     super().error(ErrorType.NAME_ERROR, "function wasnt found!!!!!!!!!!!!!!!!")
        func_def = potential[0]
        param_types = func_def.dict["param_types"]
        func_val = FunctionValue(func_def, param_types, closure_env=None)
        return Value(Type.FUNCTION, func_val)

    def get_qname_cell_and_owner(self, qname:str):
        parts = qname.split('.')
        base_name = parts[0]
        if not self.env.exists(base_name):
            super().error(ErrorType.NAME_ERROR, "variable not defined")
        if len(parts) == 1:
            cell = self.env.get_current_cell(base_name)
            if cell is None:
                super().error(ErrorType.NAME_ERROR, "variable not defined")
            return cell, None
        if self.type_from_name(base_name) != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "qualified name base is not an object")
        base_cell = self.env.get_current_cell(base_name)
        
        if base_cell is None:
            super().error(ErrorType.NAME_ERROR, "variable not defined")
        current_val = base_cell.get()
        intermediates = parts[1:-1]
        final_field = parts[-1]
        owner_object_value = None
        for field in intermediates:
            if current_val.t != Type.OBJECT:
                super().error(ErrorType.TYPE_ERROR, "intermediate of da dot is not an object")
            if current_val.v is None:
                super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted access")
            obj_fields = self.heap.get(current_val.v)
            if obj_fields is None:
                super().error(ErrorType.FAULT_ERROR, "invalid object reference")
            if field not in obj_fields:
                super().error(ErrorType.NAME_ERROR, "field not defined")
            field_cell = obj_fields[field]
            current_val = field_cell.get()
            if self.type_from_name(field) == Type.OBJECT:
                owner_object_value = current_val
        if current_val.t != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "final base of da dot is not an object")
        if current_val.v is None:
            super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted access")
        obj_fields = self.heap.get(current_val.v)
        if obj_fields is None:
            super().error(ErrorType.FAULT_ERROR, "invalid object reference")
        if final_field not in obj_fields:
            super().error(ErrorType.NAME_ERROR, "field not defined")
        return obj_fields[final_field], current_val
        
        

    def get_qname_cell(self, qname:str)->Cell:
        parts = qname.split('.')
        base_name = parts[0]
        if not self.env.exists(base_name):
            super().error(ErrorType.NAME_ERROR, "variable not defined")
        if len(parts) == 1:
            cell = self.env.get_current_cell(base_name)
            if cell is None:
                super().error(ErrorType.NAME_ERROR, "variable not defined")
            return cell

        if self.type_from_name(base_name) != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "qualified name base is not an object")
        base_cell = self.env.get_current_cell(base_name)
        
        if base_cell is None:
            super().error(ErrorType.NAME_ERROR, "variable not defined")
        current_val = base_cell.get()
        intermediates = parts[1:-1]
        final_field = parts[-1]
        for field in intermediates:
            if current_val.t != Type.OBJECT:
                super().error(ErrorType.TYPE_ERROR, "intermediate of da dot is not an object")
            if current_val.v is None:
                super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted access")
            obj_fields = self.heap.get(current_val.v)
            if obj_fields is None:
                super().error(ErrorType.FAULT_ERROR, "invalid object reference")
            if field not in obj_fields:
                super().error(ErrorType.NAME_ERROR, "field not defined")
            field_cell = obj_fields[field]
            current_val = field_cell.get()
            if self.type_from_name(field) != Type.OBJECT:
                super().error(ErrorType.TYPE_ERROR, "intermediate dotted field must be object typed")
        if current_val.t != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "final base of da dot is not an object")
        if current_val.v is None:
            super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted access")
        
        obj_fields = self.heap.get(current_val.v)
        if obj_fields is None:
            super().error(ErrorType.FAULT_ERROR, "invalid object reference")
        if final_field not in obj_fields:
            super().error(ErrorType.NAME_ERROR, "field not defined")
        return obj_fields[final_field]
    
    def interface_for_qname(self, qname:str):
        parts = qname.split(".")
        if len(parts) == 1:
            return self.interface_from_name(parts[0])
        else:
            field_name = parts[-1]
            return self.interface_from_name(field_name)
    
    def set_qname_value(self, qname:str, value:Value):
        parts = qname.split('.')
        base_name = parts[0]
        if not self.env.exists(base_name):
            super().error(ErrorType.NAME_ERROR, "variable not defined")
        if len(parts) == 1:
            left_type = self.type_from_name(base_name)
            expected_interface = self.interface_from_name(base_name)

            if value.v is None and value.t in (Type.OBJECT, Type.FUNCTION):
                if left_type in (Type.OBJECT, Type.FUNCTION):
                    value = Value(left_type, None)
                else:
                    super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment 224")
            else:
                if left_type == Type.OBJECT:
                    if value.t != Type.OBJECT:
                        super().error(ErrorType.TYPE_ERROR, "u trying to assign non object to an object !")
                elif left_type == Type.FUNCTION:
                    if value.t != Type.FUNCTION:
                        super().error(ErrorType.TYPE_ERROR, "u trying to assign non function to a function !")
                else:
                    if left_type != value.t:
                        super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment 234")

            # value_interface = getattr(value, "interface", None)
            # # if not self.compatible_interfaces(expected_interface, value_interface, value):
            # #     super().error(ErrorType.TYPE_ERROR, "interface mismatch in assignment")      
            # if(expected_interface is not None and value_interface is None and value.v is not None and
            #    value.t in (Type.OBJECT, Type.FUNCTION)):
            #     setattr(value, "interface", expected_interface)
            #     value_interface = expected_interface

            # if not self.compatible_interfaces(expected_interface, value_interface, value):
            #     super().error(ErrorType.TYPE_ERROR, "interface mismatch in assignment")

            if expected_interface is not None:
                if not self.object_satisfies_interface(expected_interface, value):
                    super().error(ErrorType.TYPE_ERROR, "interface mismatch in assignment")

            cell = self.env.get_current_cell(base_name)
            if cell is None:
                super().error(ErrorType.NAME_ERROR, "variable not defined")
            cell.set(value)
            return
            
        if self.type_from_name(base_name) != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "base of da dot assignment must be object-typed")

        base_cell = self.env.get_current_cell(base_name)
        if base_cell is None:
            super().error(ErrorType.NAME_ERROR, "variable not defined")

        current_val = base_cell.get()
        intermediates = parts[1:-1]
        final_field = parts[-1]
        for field in intermediates:
            if current_val.t != Type.OBJECT:
                super().error(ErrorType.TYPE_ERROR, "intermediate of da dot is not an object")
            if current_val.v is None:
                super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted assignment")

            obj_fields = self.heap.get(current_val.v)
            if obj_fields is None:
                super().error(ErrorType.FAULT_ERROR, "invalid object reference")
            if field not in obj_fields:
                super().error(ErrorType.NAME_ERROR, "field not defined")

            field_cell = obj_fields[field]
            current_val = field_cell.get()

            if self.type_from_name(field) != Type.OBJECT:
                super().error(ErrorType.TYPE_ERROR, "intermediate dotted field must be object typed")

        if current_val.t != Type.OBJECT:
            super().error(ErrorType.TYPE_ERROR, "final base of da dot is not an object")
        if current_val.v is None:
            super().error(ErrorType.FAULT_ERROR, "nil derefeerence in dotted assignment")

        obj_fields = self.heap.get(current_val.v)
        if obj_fields is None:
            super().error(ErrorType.FAULT_ERROR, "invalid object reference")

        final_type = self.type_from_name(final_field)
        expected_interface = self.interface_from_name(final_field)

        if value.v is None and value.t in (Type.OBJECT, Type.FUNCTION):
            if final_type in (Type.OBJECT, Type.FUNCTION):
                value = Value(final_type, None)
            else:
                super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment 284")
        else:
            if final_type == Type.OBJECT:
                if value.t != Type.OBJECT:
                    super().error(ErrorType.TYPE_ERROR, "cannot assign nonobject to object")
            elif final_type == Type.FUNCTION:
                if value.t != Type.FUNCTION:
                    super().error(ErrorType.TYPE_ERROR, "cannot assign nonfunction to function")
            else:
                if final_type != value.t:
                    super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment 294")

        # value_interface = getattr(value, "interface", None)
        # if(expected_interface is not None and value_interface is None and value.v is not None and
        #    value.t in (Type.OBJECT, Type.FUNCTION)):
        #     setattr(value, "interface", expected_interface)
        #     value_interface = expected_interface
        # if not self.compatible_interfaces(expected_interface, value_interface, value):
        #     super().error(ErrorType.TYPE_ERROR, "interface mismatch in assignment")        
        if expected_interface is not None:
            if not self.object_satisfies_interface(expected_interface, value):
                super().error(ErrorType.TYPE_ERROR, "interface mismatch in assignment")    
        if final_field in obj_fields:
            obj_fields[final_field].set(value)
        else:
            obj_fields[final_field] = Cell(value)
        # if final_type == Type.OBJECT:
        #     if value.t != Type.OBJECT:
        #         super().error(ErrorType.TYPE_ERROR, "cannot assign non-object to object field")
        # else:
        #     if final_type != value.t:
        #         super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment")

        # if final_field in obj_fields:
        #     obj_fields[final_field].set(value)
        # else:
        #     obj_fields[final_field] = Cell(value)

    def run(self, program):
        ast = parse_program(program)
        self.create_interface_table(ast)
        self.__create_function_table(ast)
        # self.__run_fcall(self.__get_function("main"))
        main_def=self.__get_function("main", tuple())
        self.current_return_type = main_def.dict["return_type"]
        self.current_return_interface = main_def.dict["return_interface"]
        self.__run_fcall(main_def)

    def default_value_for_type(self, t: Type) -> Value:
        if t == Type.INT:
            return Value(Type.INT, 0)
        if t == Type.STRING:
            return Value(Type.STRING, "")
        if t == Type.BOOL:
            return Value(Type.BOOL, False)
        if t == Type.OBJECT:
            return Value(Type.OBJECT, None)
        if t == Type.FUNCTION:
            return Value(Type.FUNCTION, None)
        if t == Type.VOID:
            return Value(Type.VOID, None)
        super().error(ErrorType.TYPE_ERROR, "unknown type for default value")

    def type_from_suffix(self, suffix: str, is_func: bool) -> Type:
        if suffix == "i":
            return Type.INT
        if suffix == "s":
            return Type.STRING
        if suffix == "b":
            return Type.BOOL
        if suffix == "o":
            return Type.OBJECT
        if suffix == "f":
            return Type.FUNCTION
        if is_func and suffix == "v":
            return Type.VOID
        if suffix.isupper() and len(suffix) == 1:
            return Type.OBJECT
        super().error(ErrorType.TYPE_ERROR, "unknown type suffix")

    def create_interface_table(self, ast):
        self.interfaces = {}
        interface_nodes = ast.get("interfaces") or []
        for interface_node in interface_nodes:
            name = interface_node.get("name")
            if not (name.isupper() and len(name) == 1 and isinstance(name,str)):
                super().error(ErrorType.NAME_ERROR, "invalid interface name")
            if name in self.interfaces:
                super().error(ErrorType.NAME_ERROR, "interface defined more than once")
            fields_info = {}
            for field in interface_node.get("fields"):
                fname = field.get("name")
                if fname in fields_info:
                    super().error(ErrorType.NAME_ERROR, "field defined more than once in interface")
                if field.elem_type == "field_var":
                    ftype = self.type_from_name(fname)
                    finterface = self.interface_from_name(fname)
                    if finterface is not None and finterface not in self.interfaces:
                        super().error(ErrorType.NAME_ERROR, "unknown interface in field var")
                    fields_info[fname] = {"kind": "var", "type": ftype, "interface": finterface}
                elif field.elem_type == "field_func":
                    params_info = []
                    for arg in field.get("params"):
                        pname = arg.get("name")
                        ptype = self.type_from_name(pname)
                        pinterface = self.interface_from_name(pname)
                        if pinterface is not None and pinterface not in self.interfaces:
                            super().error(ErrorType.NAME_ERROR, "unknown interface in field func param")
                        params_info.append({"type":ptype, "interface":pinterface, "ref":arg.get("ref")})
                    fields_info[fname] = {"kind": "func", "params": params_info}
                else:
                    super().error(ErrorType.NAME_ERROR, "unknown field type in interface")
            self.interfaces[name] = {"fields": fields_info}
    def __create_function_table(self, ast):
        self.funcs = {}
        for func in ast.get("functions"):
        #     self.funcs[(func.get("name"), len(func.get("args")))] = func
            name = func.get("name")
            args = func.get("args")

            if name == "main":
                if len(args) != 0:
                    super().error(ErrorType.NAME_ERROR, "main function cannot have parameters")
                # return_suffix = "v"
                return_type = Type.VOID
                return_interface = None
            else:
                return_suffix = name[-1]
                if return_suffix.isupper() and len(return_suffix) == 1:
                    return_type = Type.OBJECT
                    return_interface = return_suffix
                else:
                    return_type = self.type_from_suffix(return_suffix, is_func=True)
                    return_interface = None

            func.dict["return_type"] = return_type
            func.dict["return_interface"] = return_interface

            param_types: list[Type] = []
            for arg in args:
                pname = arg.get("name")
                psuffix = pname[-1]
                if psuffix.isupper() and len(psuffix) == 1:
                    ptype = Type.OBJECT
                    interface = psuffix
                else:
                    ptype = self.type_from_suffix(psuffix, is_func=False)
                    interface = None
                arg.dict["declared_type"] = ptype
                arg.dict["interface"] = interface
                param_types.append(ptype)
            func.dict["param_types"] = tuple(param_types)
            key = (name, tuple(param_types))
            if key in self.funcs:
                super().error(ErrorType.NAME_ERROR, "function defined more than once")
            self.funcs[key] = func

    def __get_function(self, name: str, param_types: tuple[Type, ...]):
        # if (name, num_params) not in self.funcs:
        #     super().error(ErrorType.NAME_ERROR, "function not found")
        # return self.funcs[(name, num_params)]
        key = (name, param_types)
        if key not in self.funcs:
            super().error(ErrorType.NAME_ERROR, "function not found")
        return self.funcs[key]

    def __run_vardef(self, statement):
        name = statement.get("name")

        vtype = self.type_from_name(name)
        initial = self.default_value_for_type(vtype)

        # interface = self.interface_from_name(name)
        # if interface is not None and initial.t in (Type.OBJECT, Type.FUNCTION):
        #     setattr(initial, "interface", interface)

        if not self.env.fdef_function(name, initial):
            super().error(ErrorType.NAME_ERROR, "variable already defined")

    def __run_bvardef(self, statement):
        name = statement.get("name")
        vtype = self.type_from_name(name)
        initial = self.default_value_for_type(vtype)
        # interface = self.interface_from_name(name)
        # if interface is not None and initial.t in (Type.OBJECT, Type.FUNCTION):
        #     setattr(initial, "interface", interface)
        if not self.env.fdef_block(name, initial):
            super().error(ErrorType.NAME_ERROR, "variable already defined")

    def __run_assign(self, statement):
        # name = statement.get("var")
        # if not self.env.exists(name):
        #     super().error(ErrorType.NAME_ERROR, "variable not defined")
        # left_val = self.env.get(name)
        # left_type = left_val.t
        # right_val = self.__eval_expr(statement.get("expression"))
        # right_type = right_val.t

        # if left_type == Type.OBJECT:
        #     if right_type != Type.OBJECT:
        #         super().error(ErrorType.TYPE_ERROR, "cannot assign non-object to object variable")
        # else:
        #     if left_type != right_type:
        #         super().error(ErrorType.TYPE_ERROR, "type mismatch in assignment")
        # if not self.env.set(name, right_val):
        #     super().error(ErrorType.NAME_ERROR, "variable not defined")
        right_val = self.__eval_expr(statement.get("expression"))
        qname = statement.get("var")
        self.set_qname_value(qname, right_val)


    def __handle_input(self, fcall_name, args):
        """Handle inputi and inputs function calls"""
        if len(args) > 1:
            super().error(ErrorType.NAME_ERROR, "too many arguments for input function")

        if args:
            self.__handle_print(args)

        res = super().get_input()

        return (
            Value(Type.INT, int(res))
            if fcall_name == "inputi"
            else Value(Type.STRING, res)
        )

    def __handle_print(self, args):
        """Handle print function calls"""
        out = ""

        for arg in args:
            c_out = self.__eval_expr(arg)
            if c_out.t == Type.BOOL:
                out += str(c_out.v).lower()
            else:
                out += str(c_out.v)

        super().output(out)

        return Value(Type.VOID, None)
    
    def invoke_function(self, func_def, args_expr_nodes, actual_args_values, closure_env=None, self_object_value=None):
        formal_params = func_def.get("args")

        if len(formal_params) != len(actual_args_values):
            super().error(ErrorType.TYPE_ERROR, "wrong number of arguments")

        bindings = []
        for formal, argument_expression, argument_value in zip(formal_params, args_expr_nodes, actual_args_values):
            pname = formal.get("name")
            declared_type = formal.dict["declared_type"]
            expected_interface = formal.dict["interface"]
            is_ref = formal.get("ref")

            # if argument_value.t != declared_type:
            #     super().error(ErrorType.TYPE_ERROR, "argument type mismatch")
            bind_val = argument_value
            if argument_value.v is None and argument_value.t in (Type.OBJECT, Type.FUNCTION):
                if declared_type in (Type.OBJECT, Type.FUNCTION):
                    bind_val = Value(declared_type, None)
                else:
                    super().error(ErrorType.TYPE_ERROR, "arg type __mismatch 477")
            else:
                if argument_value.t != declared_type:
                    super().error(ErrorType.TYPE_ERROR, "argument type mismatch")
            if expected_interface is not None:
                if not self.object_satisfies_interface(expected_interface, bind_val):
                    super().error(ErrorType.TYPE_ERROR, "argument interface mismatch")

            # value_interface = getattr(bind_val, "interface", None)
            # if(expected_interface is not None and value_interface is None and bind_val.v is not None and
            #    bind_val.t in (Type.OBJECT, Type.FUNCTION)):
            #     setattr(bind_val, "interface", expected_interface)
            #     value_interface = expected_interface
            # if not self.compatible_interfaces(expected_interface, value_interface, bind_val):
            #     super().error(ErrorType.TYPE_ERROR, "wouldnt u know :( there's an argument interface mismatch")

            if is_ref:
                if argument_expression.elem_type != self.QUALIFIED_NAME_NODE:
                    super().error(ErrorType.TYPE_ERROR, "ref argument must be a variable")
                actual_name = argument_expression.get("name")

                if expected_interface is not None:
                    arg_interface = self.interface_for_qname(actual_name)
                    if arg_interface is not None and arg_interface != expected_interface:
                        super().error(ErrorType.TYPE_ERROR, "argument interface mismatch on ref arg")

                cell = self.get_qname_cell(actual_name)
                if cell is None:
                    super().error(ErrorType.NAME_ERROR, "variable not defined")
                bindings.append(("ref", pname, cell))
            else:
                bindings.append(("val", pname, bind_val))

        previous_return_type = self.current_return_type
        previous_return_interface = self.current_return_interface
        saved_env_stack = self.env.env

        if closure_env is not None:
            self.env.env=closure_env

        self.current_return_type = func_def.dict["return_type"]
        self.current_return_interface = func_def.dict["return_interface"]

        try:
            self.env.enter_func()
            if self_object_value is not None:
                if not self.env.fdef_function("selfo", self_object_value):
                    super().error(ErrorType.NAME_ERROR, "selfo already defined? what ?????")
            for kind, pname, val in bindings:
                if kind == "val":
                    if not self.env.fdef_function(pname, val):
                        super().error(ErrorType.NAME_ERROR, "variable already defined")
                else:
                    if not self.env.fdef_function_cell(pname, val):
                        super().error(ErrorType.NAME_ERROR, "variable already defined")
            res, _ = self.__run_statements(func_def.get("statements"))
            self.env.exit_func()
        finally:
            if closure_env is not None:
                self.env.env = saved_env_stack
            self.current_return_type = previous_return_type
            self.current_return_interface = previous_return_interface

        return res

    def __run_fcall(self, func_call_ast):
        fcall_name, args = func_call_ast.get("name"), func_call_ast.get("args")

        if fcall_name == "inputi" or fcall_name == "inputs":
            return self.__handle_input(fcall_name, args)

        if fcall_name == "print":
            return self.__handle_print(args)

        actual_args = [self.__eval_expr(a) for a in args]

        for arg in actual_args:
            if arg.t == Type.VOID:
                super().error(ErrorType.TYPE_ERROR, "void value cannot be used as argument")

        has_frame = len(self.env.env)>0
        is_dotted = "." in fcall_name
        is_var = has_frame and(not is_dotted) and self.env.exists(fcall_name)

        if is_dotted or is_var:
            if is_dotted:
                func_cell, owner_object_value = self.get_qname_cell_and_owner(fcall_name)
            else:
                func_cell = self.get_qname_cell(fcall_name)
                owner_object_value = None
            func_val = func_cell.get()
            if func_val.t != Type.FUNCTION:
                super().error(ErrorType.TYPE_ERROR, "attempt to call a non-function")
            if func_val.v is None:
                super().error(ErrorType.FAULT_ERROR, "calling nil func")

            fv: FunctionValue = func_val.v
            func_def = fv.func_ast
            param_types = fv.param_types
            if len(param_types) != len(actual_args):
                super().error(ErrorType.TYPE_ERROR, "wrong number of arguments pal")
            for ptype, argval in zip(param_types, actual_args):
                if argval.t != ptype:
                    super().error(ErrorType.TYPE_ERROR, "argument type doesnt match")
            return self.invoke_function(func_def, args, actual_args, closure_env=fv.closure_env,self_object_value=owner_object_value)
        else:
            potential = []
            for (fname, ptypes), func_def in self.funcs.items():
                if fname != fcall_name:
                    continue
                if len(ptypes) != len(actual_args):
                    continue
                match = True
                for ptype, argval in zip(ptypes, actual_args):
                    is_nil_like = (argval.v is None and argval.t in (Type.OBJECT, Type.FUNCTION))
                    if is_nil_like:
                        if ptype not in (Type.OBJECT, Type.FUNCTION):
                            match = False
                            break
                    else:
                        if ptype != argval.t:
                            match = False
                            break
                if match:
                    potential.append(func_def)
            if len(potential) == 0:
                super().error(ErrorType.NAME_ERROR, "function not found")
            if len(potential) > 1:
                super().error(ErrorType.NAME_ERROR, "ambiguous function call")
            func_def = potential[0]
            return self.invoke_function(func_def, args, actual_args, closure_env=None)

            # param_types = []
            # for arg in actual_args:
            #     if arg.t == Type.NIL:
            #         param_types.append(Type.OBJECT)
            #     else:
            #         param_types.append(arg.t)
            # param_types = tuple(param_types)
            # func_def = self.__get_function(fcall_name, param_types)
            # return self.invoke_function(func_def, args, actual_args)

    def __run_if(self, statement):
        cond = self.__eval_expr(statement.get("condition"))

        if cond.t != Type.BOOL:
            super().error(ErrorType.TYPE_ERROR, "condition must be boolean")

        self.env.enter_block()

        res, ret = None, False

        if cond.v:
            res, ret = self.__run_statements(statement.get("statements"))
        elif statement.get("else_statements"):
            res, ret = self.__run_statements(statement.get("else_statements"))

        self.env.exit_block()

        return res, ret

    def __run_while(self, statement):
        res, ret = Value(), False

        while True:
            cond = self.__eval_expr(statement.get("condition"))

            if cond.t != Type.BOOL:
                super().error(ErrorType.TYPE_ERROR, "condition must be boolean")

            if not cond.v:
                break

            self.env.enter_block()
            res, ret = self.__run_statements(statement.get("statements"))
            self.env.exit_block()
            if ret:
                break

        return res, ret
    
    def capture_env_for_lambda(self):
        captured_stack = []
        for frame in self.env.env:
            new_frame = []
            for block in frame:
                new_block = {}
                for name, cell in block.items():
                    val = cell.get()
                    if val.t in (Type.INT, Type.STRING, Type.BOOL):
                        new_block[name] = Cell(Value(val.t, val.v))
                    else:
                        new_block[name] = Cell(val)
                new_frame.append(new_block)
            captured_stack.append(new_frame)
        return captured_stack

    def __run_return(self, statement):
        expr = statement.get("expression")
        expected = self.current_return_type
        expected_interface = self.current_return_interface

        if expr is None:
            if expected == Type.VOID:
                return (Value(Type.VOID, None), True)
            else:
                val = self.default_value_for_type(expected)
                if expected_interface is not None and val.t in (Type.OBJECT, Type.FUNCTION):
                    setattr(val, "interface", expected_interface)
                return (val, True)
        
        value = self.__eval_expr(expr)
        if expected == Type.VOID:
            super().error(ErrorType.TYPE_ERROR, "void func cant return a value")
        # if value.t != expected:
        #     super().error(ErrorType.TYPE_ERROR, "return type mismatch")
        if value.v is None and value.t in (Type.OBJECT, Type.FUNCTION):
            if expected in (Type.OBJECT, Type.FUNCTION):
                value = Value(expected, None)
            else:
                super().error(ErrorType.TYPE_ERROR, "return type mismatch 616")
        else:
            if value.t != expected:
                super().error(ErrorType.TYPE_ERROR, "return type mismatch")
        # value_interface = getattr(value, "interface", None)
        # if(expected_interface is not None and value_interface is None and value.v is not None and
        #    value.t in (Type.OBJECT, Type.FUNCTION)):
        #     setattr(value, "interface", expected_interface)
        #     value_interface = expected_interface
        # if not self.compatible_interfaces(expected_interface, value_interface, value):
        #     super().error(ErrorType.TYPE_ERROR, "return interface mismatch")
        if expected_interface is not None:
            if not self.object_satisfies_interface(expected_interface, value):
                super().error(ErrorType.TYPE_ERROR, "return interface mismatch")
        return (value, True)

    def __run_statements(self, statements):
        res = self.default_value_for_type(self.current_return_type)
        ret = False
        

        for statement in statements:
            kind = statement.elem_type

            if kind == self.VAR_DEF_NODE:
                self.__run_vardef(statement)
            elif kind == 'bvardef':
                self.__run_bvardef(statement)
            elif kind == "=":
                self.__run_assign(statement)
            elif kind == self.FCALL_NODE:
                self.__run_fcall(statement)
            elif kind == self.IF_NODE:
                res1, ret1 = self.__run_if(statement)
                if ret1:
                    res, ret = res1, True
                    break
            elif kind == self.WHILE_NODE:
                res1, ret1 = self.__run_while(statement)
                if ret1:
                    res, ret = res1, True
                    break
            elif kind == self.RETURN_NODE:
                res, ret = self.__run_return(statement)
                break

        return res, ret
    
    def convert_value(self, to_type: str, val: Value) -> Value:
        t = val.t
        if to_type == "int":
            if t == Type.INT:
                return val
            if t == Type.STRING:
                try:
                    return Value(Type.INT, int(val.v))
                except:
                    super().error(ErrorType.TYPE_ERROR, "cannot convert string to int")
            if t == Type.BOOL:
                return Value(Type.INT, 1 if val.v else 0)
            super().error(ErrorType.TYPE_ERROR, "invalid conversion to int")

        if to_type == "str":
            if t == Type.STRING:
                return val
            if t == Type.INT:
                return Value(Type.STRING, str(val.v))
            if t == Type.BOOL:
                return Value(Type.STRING, "true" if val.v else "false")
            super().error(ErrorType.TYPE_ERROR, "invalid conversion to string")

        if to_type == "bool":
            if t == Type.BOOL:
                return val
            if t == Type.INT:
                return Value(Type.BOOL, val.v != 0)
            if t == Type.STRING:
                return Value(Type.BOOL, val.v != "")
            super().error(ErrorType.TYPE_ERROR, "invalid conversion to bool")
        super().error(ErrorType.TYPE_ERROR, "unknown conversion type")

    def __eval_binary_op(self, kind, vl, vr):
        """Evaluate binary operations"""
        tl, tr = vl.t, vr.t
        vl_val, vr_val = vl.v, vr.v

        # if kind == "==":
        #     return Value(Type.BOOL, tl == tr and vl_val == vr_val)
        # if kind == "!=":
        #     return Value(Type.BOOL, not (tl == tr and vl_val == vr_val))
        if kind == "==" or kind == "!=":
            if self.is_nil_value(vl) and self.is_nil_value(vr):
                eq = True
            elif self.is_nil_value(vl) or self.is_nil_value(vr):
                eq = False
            elif tl == Type.OBJECT and tr == Type.OBJECT:
                eq = (vl_val == vr_val)
            elif tl == Type.FUNCTION and tr == Type.FUNCTION:
                fvl:FunctionValue = vl_val
                fvr:FunctionValue = vr_val

                is_lambda_l = (fvl.func_ast.elem_type == self.FUNC_NODE)
                is_lambda_r = (fvr.func_ast.elem_type == self.FUNC_NODE)
                # eq = (fvl.func_ast is fvr.func_ast and fvl.param_types == fvr.param_types)
                # eq = (vl_val is vr_val) #come back to this!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

                if is_lambda_l and is_lambda_r:
                    eq = (fvl is fvr)
                elif (not is_lambda_l) and (not is_lambda_r):
                    eq = (fvl.func_ast is fvr.func_ast and fvl.param_types == fvr.param_types)
                else:
                    eq = False

                # if (fvl.func_ast.elem_type == self.FUNC_NODE and
                #     fvr.func_ast.elem_type == self.FUNC_NODE):
                #     eq = (fvl is fvr)
                # elif (fvl.func_ast.elem_type != self.FUNC_NODE and
                #       fvr.func_ast.elem_type != self.FUNC_NODE):
                #     eq = (fvl.func_ast is fvr.func_ast)
                # else:
                #     eq = False
                if kind == "!=":
                    eq = not eq
                return Value(Type.BOOL, eq)
            elif tl == tr:
                eq = (vl_val == vr_val)
            else:
                eq = False
            if kind == "!=":
                eq = not eq
            return Value(Type.BOOL, eq)
            # if tl != tr:
            #     eq = False
            # else:
            #     if tl == Type.OBJECT:
            #         if vl_val is None and vr_val is None:
            #             eq = True
            #         elif vl_val is None or vr_val is None:
            #             eq = False
            #         else:
            #             eq = (vl_val == vr_val)
            #     else:
            #         eq = (vl_val == vr_val)
            # if kind == "==":
            #     return Value(Type.BOOL, eq)
            # else:
            #     return Value(Type.BOOL, not eq)

        if tl == Type.STRING and tr == Type.STRING:
            if kind == "+":
                return Value(Type.STRING, vl_val + vr_val)

        if tl == Type.INT and tr == Type.INT:
            if kind == "+":
                return Value(Type.INT, vl_val + vr_val)
            if kind == "-":
                return Value(Type.INT, vl_val - vr_val)
            if kind == "*":
                return Value(Type.INT, vl_val * vr_val)
            if kind == "/":
                return Value(Type.INT, vl_val // vr_val)
            if kind == "<":
                return Value(Type.BOOL, vl_val < vr_val)
            if kind == "<=":
                return Value(Type.BOOL, vl_val <= vr_val)
            if kind == ">":
                return Value(Type.BOOL, vl_val > vr_val)
            if kind == ">=":
                return Value(Type.BOOL, vl_val >= vr_val)

        if tl == Type.BOOL and tr == Type.BOOL:
            if kind == "&&":
                return Value(Type.BOOL, vl_val and vr_val)
            if kind == "||":
                return Value(Type.BOOL, vl_val or vr_val)

        super().error(ErrorType.TYPE_ERROR, "invalid binary operation")

    def __eval_expr(self, expr):
        kind = expr.elem_type

        if kind == self.FUNC_NODE:
            lambda_name = expr.get("name")
            return_suffix = lambda_name[-1]
            if return_suffix.isupper() and len(return_suffix) == 1:
                return_type = Type.OBJECT
                return_interface = return_suffix
            else:
                return_type = self.type_from_suffix(return_suffix, is_func=True)
                return_interface = None
            expr.dict["return_type"] = return_type
            expr.dict["return_interface"] = return_interface
            param_types: list[Type] = []
            for arg in expr.get("args"):
                pname = arg.get("name")
                psuffix = pname[-1]
                if psuffix.isupper() and len(psuffix) == 1:
                    ptype = Type.OBJECT
                    interface = psuffix
                else:
                    ptype = self.type_from_suffix(psuffix, is_func=False)
                    interface = None
                arg.dict["declared_type"] = ptype
                arg.dict["interface"] = interface
                param_types.append(ptype)
            expr.dict["param_types"] = tuple(param_types)
            closure_env = self.capture_env_for_lambda()
            fv = FunctionValue(expr, tuple(param_types), closure_env=closure_env)
            return Value(Type.FUNCTION, fv)

        if kind == self.INT_NODE:
            return Value(Type.INT, expr.get("val"))

        if kind == self.STRING_NODE:
            return Value(Type.STRING, expr.get("val"))

        if kind == self.BOOL_NODE:
            return Value(Type.BOOL, expr.get("val"))

        if kind == self.NIL_NODE:
            return Value(Type.OBJECT, None)
        
        if kind == '@':
            return self.new_object()
        
        if kind == "convert":
            target = expr.get("to_type")
            innver_val = self.__eval_expr(expr.get("expr"))
            return self.convert_value(target, innver_val)

        if kind == self.QUALIFIED_NAME_NODE:
            # var_name = expr.get("name")

            # if not self.env.exists(var_name):
            #     super().error(ErrorType.NAME_ERROR, "variable not defined")
            # return self.env.get(var_name)
            qname = expr.get("name")
            if "." in qname:
                return self.get_qname_value(qname)
            if self.env.exists(qname):
                return self.get_qname_value(qname)
            return self.make_named_function_value(qname)
            # return self.get_qname_value(qname)

        if kind == self.FCALL_NODE:
            return self.__run_fcall(expr)

        if kind in self.bops:
            l, r = self.__eval_expr(expr.get("op1")), self.__eval_expr(expr.get("op2"))
            return self.__eval_binary_op(kind, l, r)

        if kind == self.NEG_NODE:
            o = self.__eval_expr(expr.get("op1"))
            if o.t == Type.INT:
                return Value(Type.INT, -o.v)

            super().error(ErrorType.TYPE_ERROR, "cannot negate non-integer")

        if kind == self.NOT_NODE:
            o = self.__eval_expr(expr.get("op1"))
            if o.t == Type.BOOL:
                return Value(Type.BOOL, not o.v)

            super().error(ErrorType.TYPE_ERROR, "cannot apply NOT to non-boolean")

        raise Exception("should not get here!")
    
    def type_from_name(self, name: str) -> Type:
        suffix = name[-1]
        if suffix == "i":
            return Type.INT
        if suffix == "s":
            return Type.STRING
        if suffix == "b":
            return Type.BOOL
        if suffix =="o":
            return Type.OBJECT
        if suffix == "f":
            return Type.FUNCTION
        if suffix.isupper() and len(suffix) == 1:
            return Type.OBJECT
        if suffix == "v":
            super().error(ErrorType.TYPE_ERROR, "cannot have variable of void type")
        super().error(ErrorType.TYPE_ERROR, "unknown type suffix")


def main():
    interpreter = Interpreter()

    # To test your own Brewin program, place it in `test.br` and run this main function.
    with open("./test.br", "r") as f:
        program = f.read()

    interpreter.run(program)


if __name__ == "__main__":
    main()


