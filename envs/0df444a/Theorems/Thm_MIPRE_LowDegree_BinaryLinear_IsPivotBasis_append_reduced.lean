-- Prove2me | Theorems.Thm_MIPRE_LowDegree_BinaryLinear_IsPivotBasis_append_reduced
-- name    : MIPRE.LowDegree.BinaryLinear.IsPivotBasis.append_reduced
-- status  : Proved
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:57.45623+00:00
-- url     : https://prove2.me/theorems/d72c0360-77ae-4d8e-9f6e-e7523d2f01e8
-- title:
--   A reduced nonzero row can be appended at any of its nonzero coordinates
-- statement:
--   A statement of the module `MIPRE.Foundations.LowDegree.BinaryEchelon` of the MIP\* = RE formalization (commit `70cbf1c` of vidick/MIPRE-formalization). # Triangular pivot bases and certified binary reduction
--
--   A reduced nonzero row can be appended at any of its nonzero coordinates.
--
--   **Formal statement.** In Lean, with the scope shown:
--
--   ```lean
--   open MIPRE
--   open MIPRE.LowDegree
--   open MIPRE.LowDegree.BinaryLinear
--   variable {n t : ℕ}
--
--   theorem MIPRE.LowDegree.BinaryLinear.IsPivotBasis.append_reduced {b : List (Pivot n t)} (hb : IsPivotBasis b)
--       (r : Row n t) (j : Fin n) (hj : (typedReduce b r).1 j = 1) :
--       IsPivotBasis (b ++ [(j, typedReduce b r)])
--   ```
--
--   **Formalization Note** `MIPRE.LowDegree.BinaryLinear.IsPivotBasis.append_reduced` is declared in `MIPRE/Foundations/LowDegree/BinaryEchelon.lean`, lines 61–75. The binders, hypotheses and conclusion are exactly those of the Lean statement above; the uploaded statement elaborates to the same type as the declaration in the repository. The definitions it mentions are those of the published definition bundles of the module's import closure.
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/LowDegree/BinaryEchelon.lean#L61-L75

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
import Definitions.Def_MIPRE_Foundations_LowDegree_BinaryEchelon

open MIPRE
open MIPRE.LowDegree
open MIPRE.LowDegree.BinaryLinear
variable {n t : ℕ}
attribute [local instance] MIPRE.LowDegree.BinaryLinear.instFactPrimeOfNatNat_mIPRE

theorem MIPRE.LowDegree.BinaryLinear.IsPivotBasis.append_reduced {b : List (Pivot n t)} (hb : IsPivotBasis b)
    (r : Row n t) (j : Fin n) (hj : (typedReduce b r).1 j = 1) :
    IsPivotBasis (b ++ [(j, typedReduce b r)]) := by sorry
