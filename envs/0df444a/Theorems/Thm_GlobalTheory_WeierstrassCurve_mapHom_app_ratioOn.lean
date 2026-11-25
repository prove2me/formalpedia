-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_mapHom_app_ratioOn
-- name    : GlobalTheory.WeierstrassCurve.mapHom_app_ratioOn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:54:04.736974+00:00
-- url     : https://prove2.me/theorems/9897320a-8875-5ce4-929e-036a9bbf278b
-- title:
--   Weierstrass Curve: map Hom app ratio On
-- statement:
--   The Weierstrass Curve construction uses the map Hom app ratio On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L278-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L278-L282

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_SpecMapAwayFnEquivAwayChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap resG constFn)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs GlobalTheory.TangentOrigin
open GlobalTheory
open GlobalTheory.WeierstrassCurve
variable {R : Type} [CommRing R] (W : WeierstrassCurve R)
variable {R' : Type} [CommRing R'] {W' : WeierstrassCurve R'} (f : R →+* R') (h : W.map f = W')

theorem GlobalTheory.WeierstrassCurve.mapHom_app_ratioOn {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (j : Fin 3) :
    ((mapHom W f h).app U).hom (ratioOn W U i hi j) = ratioOn W' (mapHom W f h ⁻¹ᵁ U) i
      (((mapHom W f h).preimage_mono hi).trans (mapHom_preimage_coordOpen W f h i).le) j := by sorry
