-- Prove2me | Theorems.Thm_MIPRE_Cost_Machine_stepData_toData
-- name    : MIPRE.Cost.Machine.stepData_toData
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-12T16:28:38.186732+00:00
-- url     : https://prove2.me/theorems/6862437d-d97e-4811-9919-e1b351567e0c
-- title:
--   The step function on encoded configurations agrees with the evaluation machine
-- statement:
--   The evaluation machine of the ambient cost model is a small-step abstract machine (of CEK type) whose configurations $c$ consist of a *control* (either "evaluate the program $p$" or "return the value $v$"), an environment (a list of values) and a stack of continuation frames (`cons1`, `cons2`, `let1`, `loop1`, recording the pending work of a $\mathsf{cons}$, a $\mathsf{let}$ or a $\mathsf{loop}$). Its transition function is $\mathsf{step} : \mathsf{Cfg} \to \mathsf{Cfg}$, with final configurations (a returned value and an empty stack) fixed.
--
--   Configurations are encoded as data: a configuration is $\mathsf{cons}\;\mathit{ctrl}\;(\mathsf{cons}\;\mathit{env}\;\mathit{kont})$, where the control is $\mathsf{cons}\,\mathsf{nil}\,\lceil p \rceil$ ("evaluate $p$", with $\lceil p\rceil$ the tree encoding of $p$) or $\mathsf{cons}\,(\mathsf{cons}\,\mathsf{nil}\,\mathsf{nil})\,v$ ("return $v$"), and the environment and the stack are $\mathsf{cons}$-chains, each frame being $\mathsf{cons}\,(\mathsf{ofNat}\,\mathit{tag})\,\mathit{payload}$ with tags $0$ to $3$ in unary. This encoding is $c \mapsto \lceil c \rceil$, in Lean `Cfg.toData`. On data, a function $\mathsf{stepData} : \mathsf{Data} \to \mathsf{Data}$ is defined directly, using only the first-order operations $\mathsf{left}$, $\mathsf{right}$, $\mathsf{cons}$, unary decoding and list indexing, by cases on the encoded control and the encoded top frame.
--
--   For every configuration $c$,
--   $$ \mathsf{stepData}(\lceil c \rceil) = \lceil \mathsf{step}(c) \rceil . $$
--
--   The lemma transports the machine to data. It is the basis of two results: that evaluation in the ambient model is partial recursive in Mathlib's sense (the step on data is primitive recursive, `Cost/Partrec.lean`), and that the step can be implemented by a program of the model itself (`stepProg`, `Cost/Interpreter.lean`), which is the engine of the self-interpreter and hence of the efficient universal machine (blueprint `lem:universal-tm`).
--
--   **Formalization Note**: `stepData` is a total function on all data, defined by nested conditionals on `Data.unaryToNat` of tag fields and on `Data.getList` for variable lookup; the lemma only concerns its values on well-formed encodings $\lceil c \rceil$. Programs are encoded by `Prog.toData` with constructor tags $0$ to $6$ in unary, and the control, frame and configuration encodings are those of `Cost/MachineData.lean`. The iterated form `stepData^[N] (toData c) = toData (step^[N] c)` follows immediately.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/Cost/MachineData.lean#L128-L167; internal lemma of the formalization of blueprint lem:universal-tm, https://vidick.github.io/MIPRE-formalization/blueprint/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData

open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine

theorem MIPRE.Cost.Machine.stepData_toData (c : Cfg) : stepData c.toData = (step c).toData := by sorry
