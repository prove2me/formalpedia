-- Prove2me | Theorems.Thm_GlobalTheory_QuotientMeasureSigmaFinite_sigmaFinite_of_isQuotMeas
-- name    : GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:24:59.522857+00:00
-- url     : https://prove2.me/theorems/bde16f2e-c574-44de-afda-5ee169d11d08
-- title:
--   Quotient Measure Sigma Finite: sigma Finite of is Quot Meas
-- statement:
--   The Quotient Measure Sigma Finite construction uses the sigma Finite of is Quot Meas property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SigmaFiniteOfPosLintegralNeTop.lean#L33-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SigmaFiniteOfPosLintegralNeTop.lean#L33-L61

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

theorem GlobalTheory.QuotientMeasureSigmaFinite.sigmaFinite_of_isQuotMeas {k r : ℕ} {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)}
    [SigmaFinite μG] [SFinite μS] (hS : μS ≠ 0)
    (hq : PI.BesselPeriodGGP.IsQuotMeas μG μS ν) : SigmaFinite ν := by sorry
