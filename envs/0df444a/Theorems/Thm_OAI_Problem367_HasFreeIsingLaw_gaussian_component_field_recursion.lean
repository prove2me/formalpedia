-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussian_component_field_recursion
-- name    : OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:57.276586+00:00
-- url     : https://prove2.me/theorems/8c81585e-d0d2-41d5-9376-ec15d8370c1f
-- title:
--   OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion` of [lean/OAI/Probability/FreeIsing/Estimates/ComponentFieldRecursion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ComponentFieldRecursion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal BigOperators`):
--
--   ```lean
--   theorem HasFreeIsingLaw.gaussian_component_field_recursion
--       {d : ℕ} (hd : 2 ≤ d) {beta : ℝ}
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (t : ℝ≥0) (c : Fin d) :
--       let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
--       let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
--       ∀ᵐ z ∂ρ,
--         Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c))
--           (RootedBroadcast.branchRoot c) z) =
--         PlantedSymmetry.observation t z (RootedBroadcast.branchRoot c) +
--           ∑ a : {a : Fin d // c ≠ a}, cavityMessage (Real.tanh beta)
--             (Real.artanh (selectedPosterior ρ F (childComponentIndexVertex c a.1)
--               (prefixFlip c (RootedBroadcast.branchRoot a.1)) z))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ComponentIndex`, `OAI.Problem367.cavityMessage`, `OAI.Problem367.componentIndexVertex`, `OAI.Problem367.prefixFlip`, `OAI.Problem367.spinSign`, `OAI.Problem367.PlantedSymmetry.observation` and `OAI.Problem367.RootedBroadcast.branchRoot` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.childComponentIndexVertex` and `OAI.Problem367.selectedPosterior` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.exists_gaussianComponentField_critical_moment_tail` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/ComponentFieldRecursion.lean (declaration OAI.Problem367.HasFreeIsingLaw.gaussian_component_field_recursion)

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

theorem HasFreeIsingLaw.gaussian_component_field_recursion
    {d : ℕ} (hd : 2 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (t : ℝ≥0) (c : Fin d) :
    let ρ := μ.prod (PlantedSymmetry.gaussianNoiseLaw (TreeVertex d) t)
    let F : IsingSpin → ℝ → ℝ := fun s x => (t : ℝ) * spinSign s + x
    ∀ᵐ z ∂ρ,
      Real.artanh (selectedPosterior ρ F (componentIndexVertex (c := c))
        (RootedBroadcast.branchRoot c) z) =
      PlantedSymmetry.observation t z (RootedBroadcast.branchRoot c) +
        ∑ a : {a : Fin d // c ≠ a}, cavityMessage (Real.tanh beta)
          (Real.artanh (selectedPosterior ρ F (childComponentIndexVertex c a.1)
            (prefixFlip c (RootedBroadcast.branchRoot a.1)) z)) := by
  sorry

end Problem367

end

end OAI
end
