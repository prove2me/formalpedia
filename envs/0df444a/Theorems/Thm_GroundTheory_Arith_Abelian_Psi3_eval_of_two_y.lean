-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_Psi3_eval_of_two_y
-- name    : GroundTheory.Arith.Abelian.Psi3_eval_of_two_y
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:34:40.76353+00:00
-- url     : https://prove2.me/theorems/82727365-bd14-424a-a00c-ee2280e0d1ad
-- title:
--   Abelian: Psi3 eval of two y
-- statement:
--   The Abelian construction uses the Psi3 eval of two y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L176-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L176-L184

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
variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

theorem GroundTheory.Arith.Abelian.Psi3_eval_of_two_y {x y : R} (h : W.toAffine.Equation x y)
    (hy : 2 * y + W.a₁ * x + W.a₃ = 0) :
    W.Ψ₃.eval x = -(W.a₁ * y - (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)) ^ 2 := by sorry
