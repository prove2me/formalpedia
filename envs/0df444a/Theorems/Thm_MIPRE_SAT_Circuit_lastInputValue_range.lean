-- Prove2me | Theorems.Thm_MIPRE_SAT_Circuit_lastInputValue_range
-- name    : MIPRE.SAT.Circuit.lastInputValue_range
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:13:37.373205+00:00
-- url     : https://prove2.me/theorems/0f015457-250d-417f-aa91-3de4c85ebb61
-- title:
--   The executable scan reads exactly the variable selected by input-copy routing
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.InputRoutingProg` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Effective lookup of the preceding input copy. The field evaluator scans the already supplied gate/value pairs. A read of input `i` uses the last value attached to an earlier input gate for `i`, or the external input value if there is no such gate. Binary indices are compared directly; malformed large indices never cause unary expansion.
--
--   The executable scan reads exactly the variable selected by input-copy routing.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Circuit
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--   variable {α : Type*} [SizedEncoding α]
--
--   theorem MIPRE.SAT.Circuit.lastInputValue_range (C : Circuit) (k i : ℕ) (x w : ℕ → α) :
--       lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
--         i (x i) = Sum.elim x w (C.inputRef k i)
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Circuit.lastInputValue_range` is declared in `MIPRE/Foundations/SAT/InputRoutingProg.lean`, lines 48–62. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/InputRoutingProg.lean#L48-L62; blueprint lem:pcp-circuit-evaluator

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_SAT_Tseitin
import Definitions.Def_MIPRE_Foundations_SAT_GateProg
import Definitions.Def_MIPRE_Foundations_SAT_InputRouting
import Definitions.Def_MIPRE_Foundations_SAT_InputRoutingProg

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Circuit
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
variable {α : Type*} [SizedEncoding α]

theorem MIPRE.SAT.Circuit.lastInputValue_range (C : Circuit) (k i : ℕ) (x w : ℕ → α) :
    lastInputValue ((List.range k).map (fun j => (C.gates.getD j (.const false), w j)))
      i (x i) = Sum.elim x w (C.inputRef k i) := by sorry
