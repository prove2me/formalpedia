-- Prove2me | Theorems.Thm_GlobalTheory_memLp_and_tendsto_integral_inner_of_eventually_eq
-- name    : GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:49:20.058353+00:00
-- url     : https://prove2.me/theorems/21cf52b2-8747-58c8-b636-ddebbe367560
-- title:
--   Global Theory: mem Lp and tendsto integral inner of eventually eq
-- statement:
--   The Global Theory construction uses the mem Lp and tendsto integral inner of eventually eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpAndTendstoIntegralInnerOfEventuallyEq.lean#L6-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MemLpAndTendstoIntegralInnerOfEventuallyEq.lean#L6-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MemLpAndTendstoIntegralInnerOfEventuallyEq
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

theorem GlobalTheory.memLp_and_tendsto_integral_inner_of_eventually_eq : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (a : ℝ → X → E) (u : X → E) (h : X → ℝ), Integrable h μ → (∀ᶠ ε in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (a ε) μ) → (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᵐ x ∂μ, ‖a ε x‖ ^ 2 ≤ h x) → (∀ᵐ x ∂μ, ∀ᶠ ε in 𝓝[>] (0 : ℝ), a ε x = u x) → MemLp u 2 μ ∧ Tendsto (fun ε : ℝ => ∫ x, inner ℂ (a ε x) (u x) ∂μ) (𝓝[>] 0) (𝓝 (((∫ x, ‖u x‖ ^ 2 ∂μ : ℝ) : ℂ))) := by sorry
