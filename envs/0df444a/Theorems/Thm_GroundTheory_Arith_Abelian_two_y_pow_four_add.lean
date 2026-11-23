-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_two_y_pow_four_add
-- name    : GroundTheory.Arith.Abelian.two_y_pow_four_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:27.690813+00:00
-- url     : https://prove2.me/theorems/c596779d-1d76-4563-a901-cb986ffe62b0
-- title:
--   Abelian: two y pow four add
-- statement:
--   The Abelian construction uses the two y pow four add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L186-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisionPoints.lean#L186-L191

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

theorem GroundTheory.Arith.Abelian.two_y_pow_four_add {x y : R} (h : W.toAffine.Equation x y) :
    (2 * y + W.a₁ * x + W.a₃) ^ 4 + W.preΨ₄.eval x =
      (6 * x ^ 2 + W.b₂ * x + W.b₄) * W.Ψ₃.eval x := by sorry
