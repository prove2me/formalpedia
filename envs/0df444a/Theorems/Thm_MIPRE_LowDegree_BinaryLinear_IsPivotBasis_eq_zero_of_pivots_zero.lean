-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_eq_zero_of_pivots_zero
-- name    : MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:36:50.849328+00:00
-- url     : https://prove2.me/theorems/fb6640f8-39f7-4932-a815-c79a27d970d4
-- title:
--   Within the span of a triangular basis, its pivot coordinates determine the vector
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinarySolve` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Solving binary linear systems with certified elimination
--
--   Within the span of a triangular basis, its pivot coordinates determine the vector.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   open MIPRE.Cost MIPRE.Cost.PolyTimeFun
--   variable {n t : ℕ}
--
--   theorem MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
--       (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) (hz : ∀ p ∈ b, v p.1 = 0) : v = 0
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero` is declared in `MIPRE/Foundations/LowDegree/BinarySolve.lean`, lines 28–50. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinarySolve.lean#L28-L50

import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.List.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.Linarith
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
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryRepresentation
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryPolynomial
import Definitions.Def_MIPRE_Foundations_Cost_Binary
import Definitions.Def_MIPRE_Foundations_SAT_Formula
import Definitions.Def_MIPRE_Foundations_SAT_FmlLib
import Definitions.Def_MIPRE_Foundations_SAT_Flatten
import Definitions.Def_MIPRE_Foundations_Cost_Reader
import Definitions.Def_MIPRE_Foundations_SAT_FmlProg
import Definitions.Def_MIPRE_Foundations_SAT_ArrayProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryLinear
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryElimination
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasisProg
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryBasis
import Definitions.Def_MIPRE_Foundations_LowDegree_BinarySolve

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryLinear
open MIPRE.Cost MIPRE.Cost.PolyTimeFun
variable {n t : ℕ}

theorem MIPRE.LowDegree.BinaryLinear.IsPivotBasis.eq_zero_of_pivots_zero {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (v : Fin n → ZMod 2) (hv : v ∈ pivotSpan b) (hz : ∀ p ∈ b, v p.1 = 0) : v = 0 := by sorry
