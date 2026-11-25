-- Prove2me | Theorems.Thm_GlobalTheory_T_eq_zero_of_truncatedFourier_tendsto_zero_etale
-- name    : GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:32:45.132282+00:00
-- url     : https://prove2.me/theorems/58ec3850-a41e-4f41-862c-a9517cd15aea
-- title:
--   T: eq zero of truncated Fourier tendsto zero etale
-- statement:
--   The T construction uses the eq zero of truncated Fourier tendsto zero etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtaleStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTruncatedFourierTendstoZeroEtaleStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtale
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTruncatedFourierTendstoZeroEtaleStatement
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

theorem GlobalTheory.T.eq_zero_of_truncatedFourier_tendsto_zero_etale : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (μK : Measure A.K), SelfDual μK (A.kerK ψ) → ∀ (u : A.K → ℂ), IsLocallyConstant u → ∫⁻ z, ‖u z‖ₑ ^ 2 ∂μK < ⊤ → (∀ a : A.K, IsUnit a → Tendsto (fun c : F => ∫ z in {z : A.K | c • z ∈ A.OK}, u z * A.psiK ψ (-(a * z)) ∂μK) (𝓝[≠] 0) (𝓝 0)) → u = 0 := by sorry
