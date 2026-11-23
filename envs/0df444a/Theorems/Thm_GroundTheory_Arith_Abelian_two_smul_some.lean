-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_two_smul_some
-- name    : GroundTheory.Arith.Abelian.two_smul_some
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:55.088812+00:00
-- url     : https://prove2.me/theorems/238951c3-b303-4855-b7bc-8494b26cd15b
-- title:
--   Abelian: two smul some
-- statement:
--   The Abelian construction uses the two smul some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L282-L307
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L282-L307

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_NormEDS
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisionPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open scoped Polynomial.Bivariate
variable {F : Type*} [Field F] (W : WeierstrassCurve F)
variable [DecidableEq F]

theorem GroundTheory.Arith.Abelian.two_smul_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    ((2 : ℤ) • Point.some x y h = 0 ↔ 2 * y + W.a₁ * x + W.a₃ = 0) ∧
      (2 * y + W.a₁ * x + W.a₃ ≠ 0 →
        xOf W ((2 : ℤ) • Point.some x y h) * (2 * y + W.a₁ * x + W.a₃) ^ 2 =
          x * (2 * y + W.a₁ * x + W.a₃) ^ 2 - W.Ψ₃.eval x) := by sorry
