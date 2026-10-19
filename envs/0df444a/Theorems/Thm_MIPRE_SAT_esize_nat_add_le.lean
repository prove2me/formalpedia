-- Prove2me | Theorems.Thm_MIPRE_SAT_esize_nat_add_le
-- name    : MIPRE.SAT.esize_nat_add_le
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:17:01.233161+00:00
-- url     : https://prove2.me/theorems/7a6fdaa2-2037-4a13-b2dd-abea43b4a94e
-- title:
--   Lemma esize_nat_add_le of the MIP* = RE formalization
-- statement:
--   A statement of the module `MIPRE.Foundations.SAT.Flatten` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). Flattening a formula to a circuit, in polynomial time. A formula is encoded as its post-order serialization (`Fml.rpn`), and the circuit of a formula (`Fml.flattenAt 0`) is computed from that serialization by a single left-to-right scan with a stack of gate indices (`flStep`, `flatten`): an input or constant node emits its gate and pushes the gate's index; a connective pops the indices of its arguments, emits the gate and pushes the new index. The scan is a fold, so the program is a `PolyTimeFun.foldl` of the step (`PolyTimeFun.casesNode` dispatches on the node), and `Fml.toCircuitF` is the…
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.SAT
--   open MIPRE.Cost Polynomial
--
--   theorem MIPRE.SAT.esize_nat_add_le (n k : ℕ) : esize (n + k) ≤ esize n + 4 * k
--   ```
--
--   **Formalization Note** `MIPRE.SAT.esize_nat_add_le` is declared in `MIPRE/Foundations/SAT/Flatten.lean`, lines 123–126. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/SAT/Flatten.lean#L123-L126

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
import Definitions.Def_MIPRE_Foundations_SAT_Flatten

open MIPRE
open MIPRE.SAT
open MIPRE.Cost Polynomial

theorem MIPRE.SAT.esize_nat_add_le (n k : ℕ) : esize (n + k) ≤ esize n + 4 * k := by sorry
