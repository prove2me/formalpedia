-- Prove2me | Theorems.Thm_GlobalTheory_QuotientMeasureSigmaFinite_sigmaFinite_of_pos_lintegral_ne_top
-- name    : GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_pos_lintegral_ne_top
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:33.710377+00:00
-- url     : https://prove2.me/theorems/8016b91b-5d6e-41d0-8408-dba518c32f00
-- title:
--   Quotient Measure Sigma Finite: sigma Finite of pos lintegral ne top
-- statement:
--   The Quotient Measure Sigma Finite construction uses the sigma Finite of pos lintegral ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SigmaFiniteOfPosLintegralNeTop.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SigmaFiniteOfPosLintegralNeTop.lean#L11-L24

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_SideNormalisedGap
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_KFinDecayOfDecInf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SigmaFiniteOfPosLintegralNeTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.QuotientMeasureSigmaFinite

theorem GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_pos_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {g : X → ℝ≥0∞} (hg : Measurable g) (hpos : ∀ x, g x ≠ 0) (hfin : ∫⁻ x, g x ∂ν ≠ ∞) :
    SigmaFinite ν := by sorry
