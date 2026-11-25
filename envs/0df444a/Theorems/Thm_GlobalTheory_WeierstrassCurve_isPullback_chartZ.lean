-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isPullback_chartZ
-- name    : GlobalTheory.WeierstrassCurve.isPullback_chartZ
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:23.562928+00:00
-- url     : https://prove2.me/theorems/746f85be-cf76-4f8b-96e3-2949098e9c1d
-- title:
--   Weierstrass Curve: is Pullback chart Z
-- statement:
--   The Weierstrass Curve construction uses the is Pullback chart Z property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1107-L1111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1107-L1111

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

theorem GlobalTheory.WeierstrassCurve.isPullback_chartZ : IsPullback (Spec.map (CommRingCat.ofHom (affineMap W f h)))
    (chartZ W') (chartZ W) (mapHom W f h) := by sorry
