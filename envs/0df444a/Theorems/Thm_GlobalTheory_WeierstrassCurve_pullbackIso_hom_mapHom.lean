-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_pullbackIso_hom_mapHom
-- name    : GlobalTheory.WeierstrassCurve.pullbackIso_hom_mapHom
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:42:53.964776+00:00
-- url     : https://prove2.me/theorems/645951a7-fa1b-5640-b577-0e59aac122a1
-- title:
--   Weierstrass Curve: pullback Iso hom map Hom
-- statement:
--   The Weierstrass Curve construction uses the pullback Iso hom map Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1123-L1125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/OpensRangeChartYSupOpensRangeChartZ.lean#L1123-L1125

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

theorem GlobalTheory.WeierstrassCurve.pullbackIso_hom_mapHom :
    (pullbackIso W f h).hom ≫ mapHom W f h = pullback.fst _ _ := by sorry
