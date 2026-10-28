-- Prove2me | Theorems.Thm_OAI_Rokhlin_ArrayObjects_compact_zero_entropy_no_witness
-- name    : OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-26T06:46:11.848586+00:00
-- url     : https://prove2.me/theorems/d0198119-9dc6-4a1d-996f-9ad7904304ca
-- title:
--   OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness: intermediate lemma from OpenAI, Rokhlin's multiple-mixing problem for one transformation
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Rokhlin.mixing_all_finite_orders`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Rokhlin's multiple-mixing problem for one transformation*, OpenAI Math Release, September 23, 2026, result family 145, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness` of [lean/OAI/Dynamics/MultipleMixing/MultipleMixing/WeakLimits.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/WeakLimits.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Rokhlin.ArrayObjects`, with `open MeasureTheory ProbabilityTheory Filter TopologicalSpace`, `open scoped Topology BigOperators`):
--
--   ```lean
--   lemma compact_zero_entropy_no_witness (hk : 3 ≤ Fintype.card I)
--       (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
--         Tendsto (fun n => (μ : Measure X) (A ∩ (T^[n]) ⁻¹' B)) atTop
--           (𝓝 ((μ : Measure X) A * (μ : Measure X) B)))
--       {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
--       (α : X → A) (hα : Measurable α) (v : A → ℝ)
--       (hcenter : ∫ x, v (α x) ∂(μ : Measure X) = 0)
--       (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := (μ : Measure X))
--         (fun m x => α ((T^[m]) x)) n / n) atTop (𝓝 0))
--       (i : I) (f : I → C(X,ℝ)) (hb : ∀ j x, |f j x| ≤ 1)
--       (hi : ∀ x, f i x = v (α x)) (δ : ℝ) (hδ : 0 < δ)
--       (hc : ∀ b, δ ≤ ∫ x, ∏ j, f j ((T^[d b j]) x) ∂(μ : Measure X)) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.Rokhlin.ArrayObjects.StandardSpace` and `OAI.Rokhlin.ArrayObjects.instMeasurableSpaceα` (definitions bundle `OAIQ3Ro000` of this split); `OAI.Rokhlin.wordEntropy` (definitions bundle `OAIQ3Ro001` of this split).
--
--   **Used by.** The proof of `OAI.Rokhlin.tail_finite_correlation_zero` of this split imports it.
-- source:
--   OpenAI, Rokhlin's multiple-mixing problem for one transformation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 145; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Rokhlins-multiple-mixing-problem-for-one-transformation-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Dynamics/MultipleMixing/MultipleMixing/WeakLimits.lean (declaration OAI.Rokhlin.ArrayObjects.compact_zero_entropy_no_witness)

import Mathlib
import Definitions.Def_OAIQ3Ro000
import Definitions.Def_OAIQ3Ro001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Rokhlin

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology BigOperators
namespace ArrayObjects
universe u
variable {I : Type u} [Fintype I] [retained15 : DecidableEq I]
    {X : StandardSpace.{u}} [TopologicalSpace X] [retained16 : CompactSpace X] [retained17 : T2Space X]
    [SecondCountableTopology X] [retained18 : MetrizableSpace X] [BorelSpace X]
    (T : X ≃ₜ X) (d : ℕ → I → ℕ) (μ : ProbabilityMeasure X)

variable (hμ : MeasurePreserving T μ μ)
    (hrect : ∀ J : Finset I, J ≠ Finset.univ → ∀ s : J → Set X,
      (∀ j, MeasurableSet (s j)) → Tendsto
        (fun b => (μ : Measure X) (⋂ j : J, (T^[d b j]) ⁻¹' s j)) atTop
        (𝓝 (∏ j : J, (μ : Measure X) (s j))))

include hμ hrect in

lemma compact_zero_entropy_no_witness (hk : 3 ≤ Fintype.card I)
    (hmix : ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
      Tendsto (fun n => (μ : Measure X) (A ∩ (T^[n]) ⁻¹' B)) atTop
        (𝓝 ((μ : Measure X) A * (μ : Measure X) B)))
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (α : X → A) (hα : Measurable α) (v : A → ℝ)
    (hcenter : ∫ x, v (α x) ∂(μ : Measure X) = 0)
    (hH : Tendsto (fun n : ℕ => Rokhlin.wordEntropy (η := (μ : Measure X))
      (fun m x => α ((T^[m]) x)) n / n) atTop (𝓝 0))
    (i : I) (f : I → C(X,ℝ)) (hb : ∀ j x, |f j x| ≤ 1)
    (hi : ∀ x, f i x = v (α x)) (δ : ℝ) (hδ : 0 < δ)
    (hc : ∀ b, δ ≤ ∫ x, ∏ j, f j ((T^[d b j]) x) ∂(μ : Measure X)) : False := by
  sorry
end ArrayObjects

end Rokhlin

end

end OAI
end
