-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_lintegral_concKernel_mul_zero
-- name    : GlobalTheory.tendsto_lintegral_concKernel_mul_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:22:29.303843+00:00
-- url     : https://prove2.me/theorems/30e5bc1b-393e-47a9-bdcb-c7b3a8c2ac6f
-- title:
--   Global Theory: tendsto lintegral conc Kernel mul zero
-- statement:
--   The Global Theory construction uses the tendsto lintegral conc Kernel mul zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoLintegralPoissonKernelBoundary.lean#L34-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TendstoLintegralPoissonKernelBoundary.lean#L34-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TendstoLintegralPoissonKernelBoundary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory

theorem GlobalTheory.tendsto_lintegral_concKernel_mul_zero :
    ∀ (M : Type) [TopologicalSpace M] [T2Space M] [MeasurableSpace M] [BorelSpace M] (ν : Measure M) (K : Set M) (v D : M → ℝ) (C : ENNReal),
    IsCompact K → ContinuousOn v K → ContinuousOn D K → (∀ z ∈ K, v z = 1 → D z = 0) → C ≠ ⊤ →
    Measure.map v (ν.restrict K) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) →
    Filter.Tendsto (fun t : ℝ => ∫⁻ z in K, ENNReal.ofReal (t / (1 - v z + t) ^ 2 * D z) ∂ν) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by sorry
