-- Prove2me | Theorems.Thm_GlobalTheory_memLp_two_and_tendsto_of_cauchy_of_ae_tendsto
-- name    : GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:35.025463+00:00
-- url     : https://prove2.me/theorems/c23617a3-8a8f-4b9e-9336-a70c8fbcd484
-- title:
--   Global Theory: mem Lp two and tendsto of cauchy of ae tendsto
-- statement:
--   The Global Theory construction uses the mem Lp two and tendsto of cauchy of ae tendsto property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpTwoAndTendstoOfCauchyOfAeTendsto.lean#L18-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpTwoAndTendstoOfCauchyOfAeTendsto.lean#L18-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MemLpTwoAndTendstoOfCauchyOfAeTendsto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology
open GlobalTheory

theorem GlobalTheory.memLp_two_and_tendsto_of_cauchy_of_ae_tendsto :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] (v : ℕ → X → E) (u : X → E) (K : ℝ), (∀ n, MemLp (v n) 2 μ) → (∀ᵐ x ∂μ, Tendsto (fun n => v n x) atTop (𝓝 (u x))) → (∀ n m : ℕ, n ≤ m → ∫ x, ‖v n x - v m x‖ ^ 2 ∂μ ≤ K / ((n : ℝ) + 1)) → MemLp u 2 μ ∧ Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) := by sorry
