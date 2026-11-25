-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isPullback_chartY
-- name    : GlobalTheory.WeierstrassCurve.isPullback_chartY
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:13:40.377872+00:00
-- url     : https://prove2.me/theorems/cb051655-a0b4-444d-b919-0d64de662225
-- title:
--   Weierstrass Curve: is Pullback chart Y
-- statement:
--   The Weierstrass Curve construction uses the is Pullback chart Y property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1113-L1117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1113-L1117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_AwayLiftCompFromZeroRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal Limits
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
attribute [local instance] MvPolynomial.gradedAlgebra
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable {R' R'' : Type u} [CommRing R'] [CommRing R''] {W' : WeierstrassCurve R'}
  {W'' : WeierstrassCurve R''}
variable (f : R →+* R') (h : W.map f = W')

theorem GlobalTheory.WeierstrassCurve.isPullback_chartY : IsPullback (Spec.map (CommRingCat.ofHom (originMap W f h)))
    (chartY W') (chartY W) (mapHom W f h) := by sorry
