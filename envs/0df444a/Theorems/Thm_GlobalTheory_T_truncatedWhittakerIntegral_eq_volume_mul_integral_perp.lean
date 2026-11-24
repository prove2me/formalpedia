-- Prove2me | Theorems.Thm_GlobalTheory_T_truncatedWhittakerIntegral_eq_volume_mul_integral_perp
-- name    : GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:00:05.922542+00:00
-- url     : https://prove2.me/theorems/f6e63b6a-c7d3-4715-b21f-9b8fbd46e51f
-- title:
--   T: truncated Whittaker Integral eq volume mul integral perp
-- statement:
--   The T construction uses the truncated Whittaker Integral eq volume mul integral perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement.lean#L11-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement.lean#L11-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerIntegralEqVolumeMulIntegralPer
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteNormedAlgebraEqModuleTopology
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TruncatedWhittakerIntegralEqVolumeMulIntegralPerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.truncatedWhittakerIntegral_eq_volume_mul_integral_perp : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), μK.IsAddHaarMeasure → ∀ (φ' : A.K × A.K → ℂ), IsTest φ' → ∀ (a : A.K) (c : F), c ≠ 0 → ∫ z in {z : A.K | c • z ∈ A.OK}, (∫ t, (∫ b, φ' (b, t) * A.psiK ψ (t * z * b) ∂μK) * A.etaK t ∂μK) * A.psiK ψ (-(a * z)) ∂μK = (((μK {z : A.K | c • z ∈ A.OK}).toReal : ℝ) : ℂ) * ∫ t, (∫ b, φ' (b, t) * Set.indicator {y : A.K | ∀ x : A.K, c • x ∈ A.OK → A.psiK ψ (x * y) = 1} (fun _ => (1 : ℂ)) (t * b - a) ∂μK) * A.etaK t ∂μK := by sorry
