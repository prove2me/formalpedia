-- Prove2me | Theorems.Thm_GroundTheory_Arith_Abelian_span_X_sub_C_le_comap_XYIdeal
-- name    : GroundTheory.Arith.Abelian.span_X_sub_C_le_comap_XYIdeal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:25:30.103689+00:00
-- url     : https://prove2.me/theorems/54291acc-ff09-47e8-a933-bf29f88a3927
-- title:
--   Abelian: span X sub C le comap XYIdeal
-- statement:
--   The Abelian construction uses the span X sub C le comap XYIdeal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/AbelianVarieties/DivisorsNorm.lean#L26-L30

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_Divisors
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_DivisorsNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Abelian
open Polynomial WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing
  IsDedekindDomain
open scoped nonZeroDivisors
universe u
variable {F : Type u} [Field F] (W : WeierstrassCurve F)

theorem GroundTheory.Arith.Abelian.span_X_sub_C_le_comap_XYIdeal (x : F) (y : F[X]) :
    Ideal.span {X - C x} ≤ (XYIdeal W.toAffine x y).comap (algebraMap F[X] _) := by sorry
