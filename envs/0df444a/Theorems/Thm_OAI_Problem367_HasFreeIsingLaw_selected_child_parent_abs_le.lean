-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_selected_child_parent_abs_le
-- name    : OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:43.313803+00:00
-- url     : https://prove2.me/theorems/c48fd629-9387-4e6d-a8a8-c30ac96749f5
-- title:
--   OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le` of [lean/OAI/Probability/FreeIsing/Estimates/ComponentFusionRecurrence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ComponentFusionRecurrence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   theorem HasFreeIsingLaw.selected_child_parent_abs_le
--       {d : ℕ} {theta : ℝ} {A B : Type*}
--       [MeasurableSpace A] [StandardBorelSpace A]
--       [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
--       {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
--       (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
--       (ν : Measure A) [IsProbabilityMeasure ν]
--       {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
--       ∀ᵐ z ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
--         |selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
--           F (childComponentIndexVertex c a) (RootedBroadcast.branchRoot c) z| ≤ theta
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ComponentIndex` and `OAI.Problem367.RootedBroadcast.branchRoot` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.childComponentIndexVertex` and `OAI.Problem367.selectedPosterior` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments`, `OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero` and `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ComponentFusionRecurrence.lean (declaration OAI.Problem367.HasFreeIsingLaw.selected_child_parent_abs_le)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationFactor.kernel_markov _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace Problem367

theorem HasFreeIsingLaw.selected_child_parent_abs_le
    {d : ℕ} {theta : ℝ} {A B : Type*}
    [MeasurableSpace A] [StandardBorelSpace A]
    [MeasurableSpace B] [StandardBorelSpace B] [Nonempty B]
    {μ : Measure (TreeVertex d → IsingSpin)} (hμ : HasFreeIsingLaw theta μ)
    (h0 : 0 ≤ theta) (h1 : theta ≤ 1)
    (ν : Measure A) [IsProbabilityMeasure ν]
    {F : IsingSpin → A → B} (hF : Measurable (Function.uncurry F)) (c a : Fin d) :
    ∀ᵐ z ∂μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)),
      |selectedPosterior (μ.prod (Measure.infinitePi (fun _ : TreeVertex d => ν)))
        F (childComponentIndexVertex c a) (RootedBroadcast.branchRoot c) z| ≤ theta := by
  sorry

end Problem367

end

end OAI
end
