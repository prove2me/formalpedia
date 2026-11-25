-- Prove2me | Theorems.Thm_GlobalTheory_WeierstrassCurve_eq_ptHom_evalPt
-- name    : GlobalTheory.WeierstrassCurve.eq_ptHom_evalPt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:53:32.50634+00:00
-- url     : https://prove2.me/theorems/cff557b3-d707-48dc-b2c2-f131f603c3f0
-- title:
--   Weierstrass Curve: eq pt Hom eval Pt
-- statement:
--   The Weierstrass Curve construction uses the eq pt Hom eval Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L177-L188
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L177-L188

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
variable {W} {A : Type} [CommRing A]

theorem GlobalTheory.WeierstrassCurve.eq_ptHom_evalPt {x : Sp A ⟶ scheme W} {ρ : R →+* A} (hx : x ≫ toSpec W = spMap ρ)
    {U : (scheme W).Opens} {i : Fin 3} (hi : U ≤ coordOpen W i) (h : ⊤ ≤ x ⁻¹ᵁ U)
    {P : Fin 3 → A} (hP : ∀ j, evalPt x U h (ratioOn W U i hi j) = P j) :
    ∃ hP, x = ptHom W ρ P hP := by sorry
