-- Prove2me | Theorems.Thm_GlobalTheory_tendsto_integral_inner_of_tendsto_eLpNorm_two
-- name    : GlobalTheory.tendsto_integral_inner_of_tendsto_eLpNorm_two
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:51:54.219647+00:00
-- url     : https://prove2.me/theorems/3c834b36-ecda-4fb9-861a-4d3a46398161
-- title:
--   Global Theory: tendsto integral inner of tendsto e Lp Norm two
-- statement:
--   The Global Theory construction uses the tendsto integral inner of tendsto e Lp Norm two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TendstoIntegralInnerOfTendstoELpNormTwo.lean#L7-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/TendstoIntegralInnerOfTendstoELpNormTwo.lean#L7-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_TendstoIntegralInnerOfTendstoELpNormTwo
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

theorem GlobalTheory.tendsto_integral_inner_of_tendsto_eLpNorm_two :
    ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (v v' : ℕ → X → E) (u u' : X → E), (∀ n, MemLp (v n) 2 μ) → (∀ n, MemLp (v' n) 2 μ) → MemLp u 2 μ → MemLp u' 2 μ → Tendsto (fun n => eLpNorm (v n - u) 2 μ) atTop (𝓝 0) → Tendsto (fun n => eLpNorm (v' n - u') 2 μ) atTop (𝓝 0) → Tendsto (fun n => ∫ x, inner ℂ (v' n x) (v n x) ∂μ) atTop (𝓝 (∫ x, inner ℂ (u' x) (u x) ∂μ)) := by sorry
