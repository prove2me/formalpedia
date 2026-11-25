-- Prove2me | Theorems.Thm_GlobalTheory_coeff_eq_zero_of_simple_pole
-- name    : GlobalTheory.coeff_eq_zero_of_simple_pole
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:50:01.580038+00:00
-- url     : https://prove2.me/theorems/388a2222-a8f2-47ed-a1cc-c4384b316ab5
-- title:
--   Global Theory: coeff eq zero of simple pole
-- statement:
--   The Global Theory construction uses the coeff eq zero of simple pole property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L19-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AbelianSchemeLaws/SpecMapAwayFnEquivAwayChart.lean#L19-L57

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

theorem GlobalTheory.coeff_eq_zero_of_simple_pole {R B C κ : Type*} [CommRing R] [CommRing B] [CommRing C]
    (ρ : R →+* B) (ι : B →+* C) (hι : Function.Injective ι) (ε : B →+* R)
    (hρ : ∀ r, ε (ρ r) = r) (z : B) (hz : ε z = 0) (d : κ → ℕ) (hd : Function.Injective d)
    (e : κ → C) (v : κ → B) (hv : ∀ k, ι z ^ d k * e k = ι (v k)) (hε : ∀ k, ε (v k) = 1)
    (c : κ → R) (s : Finset κ) (b : B) (h : ι z * ∑ k ∈ s, ι (ρ (c k)) * e k = ι b) :
    ∀ k ∈ s, 2 ≤ d k → c k = 0 := by sorry
