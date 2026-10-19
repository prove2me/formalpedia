-- Prove2me | Theorems.Thm_MIPRE_SAT_Fml_exists_circuit
-- name    : MIPRE.SAT.Fml.exists_circuit
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T00:27:18.189327+00:00
-- url     : https://prove2.me/theorems/3c251fb0-89e8-4d29-992d-70e1728f7426
-- title:
--   Every Boolean function on N bits is computed by a well-formed circuit on N inputs of at most 7 · 2^N gates
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Table` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Every Boolean function has a circuit. The formula of a Boolean function on `N` bits from its truth table (`Fml.table`): a mux tree on the bits, of size at most `7 · 2^N`. Its circuit is well-formed (`Fml.toCircuit_wellFormed`) and computes the function (`Fml.eval_table`). This is how the check circuit of the Cook–Levin tableau of the interpreter machine is obtained: from the truth table of the local check predicate, as in the paper's `lem:pack-check-size` (`planning/succinct-cook-levin.md`, S3).
--
--   **Every Boolean function on `N` bits is computed by a well-formed circuit on `N` inputs**
--   of at most `7 · 2^N` gates.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.SAT.Fml
--
--   theorem MIPRE.SAT.Fml.exists_circuit (N : ℕ) (f : (Fin N → Bool) → Bool) :
--       ∃ C : Circuit, C.WellFormed ∧ C.inputs = N ∧ C.size ≤ 7 * 2 ^ N ∧
--         ∀ x : Fin N → Bool, C.evalBits (List.ofFn x) = f x
--   ```
--
--   **Formalization Note** `MIPRE.SAT.Fml.exists_circuit` is declared in `MIPRE/Foundations/SAT/Table.lean`, lines 66–77. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Table.lean#L66-L77

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_Table

open MIPRE
open MIPRE.SAT
open MIPRE.SAT.Fml

theorem MIPRE.SAT.Fml.exists_circuit (N : ℕ) (f : (Fin N → Bool) → Bool) :
    ∃ C : Circuit, C.WellFormed ∧ C.inputs = N ∧ C.size ≤ 7 * 2 ^ N ∧
      ∀ x : Fin N → Bool, C.evalBits (List.ofFn x) = f x := by sorry
