-- Prove2me | Theorems.Thm_GlobalTheory_jHyp_wn
-- name    : GlobalTheory.jHyp_wn
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:03:05.415357+00:00
-- url     : https://prove2.me/theorems/69fdc476-dcd5-43f9-9225-6ce21d5291c5
-- title:
--   Global Theory: j Hyp wn
-- statement:
--   The Global Theory construction uses the j Hyp wn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedWhittakerJHypEqOrbitalIntegral.lean#L31-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedWhittakerJHypEqOrbitalIntegral.lean#L31-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DualCinvOKSmallStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EventuallyTestFunctionMulInverseUnitEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_VolumeScaledIntegersMulVolumeDualEqOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerJHypEqOrbitalIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory

theorem GlobalTheory.jHyp_wn : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ) (z : A.K), A.jHyp μK ψ φ' (wS A.K * nS z) = ∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK := by sorry
