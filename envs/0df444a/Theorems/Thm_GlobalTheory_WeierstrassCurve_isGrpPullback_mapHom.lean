-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_isGrpPullback_mapHom
-- name    : GlobalTheory.WeierstrassCurve.isGrpPullback_mapHom
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:03:26.360523+00:00
-- url     : https://prove2.me/theorems/71e13d8c-1fd7-42a8-b6db-9e8c60b59a2b
-- title:
--   Weierstrass Curve: is Grp Pullback map Hom
-- statement:
--   The Weierstrass Curve construction uses the is Grp Pullback map Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L260-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/ExistsLiftAddOfIsReducedEq.lean#L260-L266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IrrelevantLeMapLinearGradedMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsLiftAddOfIsReducedEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
universe u
noncomputable section
open GlobalTheory
open GlobalTheory.WeierstrassCurve
open AddLaw
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [W.IsElliptic]

theorem GlobalTheory.WeierstrassCurve.isGrpPullback_mapHom {R R' : Type} [CommRing R] [CommRing R'] (W : WeierstrassCurve R)
    [W.IsElliptic] {W' : WeierstrassCurve R'} [W'.IsElliptic] (f : R →+* R') (h : W.map f = W') :
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (schemeOver W') (schemeOver W)
      (Spec.map (CommRingCat.ofHom f)) (mapHom W f h) := by sorry
