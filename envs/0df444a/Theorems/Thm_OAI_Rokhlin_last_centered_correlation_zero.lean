-- Prove2me | Theorems.Thm_OAI_Rokhlin_last_centered_correlation_zero
-- name    : OAI.Rokhlin.last_centered_correlation_zero
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:36:07.560189+00:00
-- url     : https://prove2.me/theorems/5853260f-c209-4b0e-8d0e-82a7c720ed62
-- title:
--   OAI.Rokhlin.last_centered_correlation_zero: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.last_centered_correlation_zero` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators`):
--
--   ```lean
--   theorem last_centered_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
--       (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
--       (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
--         Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
--       (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
--       (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
--         (∀ j, MeasurableSet (s j)) → Tendsto
--           (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
--           (𝓝 (∏ j : J, μ (s j))))
--       (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
--       (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
--       (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
--       Tendsto (fun r => ∫ x, (f i (a ((T^[d r i]) x))-∫ y, f i (a y) ∂μ) *
--         ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0)
--   ```
--
--   **Used by.** The proof of `OAI.Rokhlin.sequential_mixing_all` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/Tail.lean (declaration OAI.Rokhlin.last_centered_correlation_zero)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

open MeasureTheory Filter
open scoped Topology BigOperators
variable {Ω : Type*} {I A : Type} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [Fintype A] [Nonempty A] [MeasurableSpace A] [MeasurableSingletonClass A]
    [TopologicalSpace A] [DiscreteTopology A] [BorelSpace A]

theorem last_centered_correlation_zero (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω ≃ᵐ Ω) (hT : MeasurePreserving T μ μ)
    (hmix : ∀ s t : Set Ω, MeasurableSet s → MeasurableSet t →
      Tendsto (fun n : ℕ => μ (s ∩ (T^[n]) ⁻¹' t)) atTop (𝓝 (μ s*μ t)))
    (hk : 3 ≤ Fintype.card I) (d : ℕ → I → ℕ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set Ω,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun r => μ (⋂ j : J, (T^[d r j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, μ (s j))))
    (i : I) (hremote : ∀ r j, j ≠ i → d r j+r < d r i)
    (a : Ω → A) (ha : Measurable a) (f : I → A → ℝ)
    (hf : ∀ j z, f j z ∈ Set.Icc (0:ℝ) 1) :
    Tendsto (fun r => ∫ x, (f i (a ((T^[d r i]) x))-∫ y, f i (a y) ∂μ) *
      ∏ j ∈ Finset.univ.erase i, f j (a ((T^[d r j]) x)) ∂μ) atTop (𝓝 0) := by
  sorry

end Rokhlin

end

end OAI
end
