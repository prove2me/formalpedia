-- Prove2me | Theorems.Thm_MIPRE_LowDegree_DegreeArithmetic_mem_descendingUnary_iff
-- name    : MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T01:15:09.187741+00:00
-- url     : https://prove2.me/theorems/ef60b73f-01dc-4dbd-87a0-b5d9f3bb8275
-- title:
--   A unary value occurs in the descending enumeration exactly when it is bounded by the input
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.UnaryDegreeArithmetic` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Polynomial-time unary arithmetic for degree decomposition
--
--   A unary value occurs in the descending enumeration exactly when it is bounded by the input.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.DegreeArithmetic
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial
--
--   theorem MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff (u d : Unary) : d ∈ descendingUnary u ↔ d.length ≤ u.length
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff` is declared in `MIPRE/Foundations/LowDegree/UnaryDegreeArithmetic.lean`, lines 151–163. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/UnaryDegreeArithmetic.lean#L151-L163

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Fold
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_Cost_Iterates
import Definitions.Def_MIPRE_Foundations_LowDegree_UnaryDegreeArithmetic

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.DegreeArithmetic
open MIPRE.Cost MIPRE.Cost.PolyTimeFun Polynomial

theorem MIPRE.LowDegree.DegreeArithmetic.mem_descendingUnary_iff (u d : Unary) : d ∈ descendingUnary u ↔ d.length ≤ u.length := by sorry
