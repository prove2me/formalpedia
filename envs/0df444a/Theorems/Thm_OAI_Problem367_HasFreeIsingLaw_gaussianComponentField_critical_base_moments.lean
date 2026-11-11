-- Prove2me | Theorems.Thm_OAI_Problem367_HasFreeIsingLaw_gaussianComponentField_critical_base_moments
-- name    : OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:41:21.861411+00:00
-- url     : https://prove2.me/theorems/374cb4d0-8015-41b1-9ce0-86275878c755
-- title:
--   OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments` of [lean/OAI/Probability/FreeIsing/Energy/SelectedCriticalFieldMoments.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Energy/SelectedCriticalFieldMoments.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal`, `open PlantedSymmetry`):
--
--   ```lean
--   theorem HasFreeIsingLaw.gaussianComponentField_critical_base_moments
--       {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
--       {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
--       (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d)
--       (p : ℕ) (hp : p < 3) :
--       (∫ q, |selectedGaussianField μ t (componentIndexVertex (c := c))
--         (RootedBroadcast.branchRoot c) q| ^ p
--         ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
--         Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
--           (t : ℝ) ^ ((p : ℝ) / 4)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ComponentIndex`, `OAI.Problem367.componentIndexVertex` and `OAI.Problem367.RootedBroadcast.branchRoot` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.criticalComponentBaseExponent` and `OAI.Problem367.PlantedSymmetry.gaussianNoiseLaw` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.selectedGaussianField` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.exists_gaussianComponentField_critical_moment_tail` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Energy/SelectedCriticalFieldMoments.lean (declaration OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments)

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

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Problem367

open PlantedSymmetry

theorem HasFreeIsingLaw.gaussianComponentField_critical_base_moments
    {d : ℕ} (hd : 3 ≤ d) {beta : ℝ}
    {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * (Real.tanh beta) ^ 2 = 1)
    (t : ℝ≥0) (ht : (t : ℝ) ≤ 1) (c : Fin d)
    (p : ℕ) (hp : p < 3) :
    (∫ q, |selectedGaussianField μ t (componentIndexVertex (c := c))
      (RootedBroadcast.branchRoot c) q| ^ p
      ∂μ.prod (gaussianNoiseLaw (TreeVertex d) t)) ≤
      Real.exp (criticalComponentBaseExponent d beta * (p : ℝ) ^ 2) *
        (t : ℝ) ^ ((p : ℝ) / 4) := by
  sorry

end Problem367

end

end OAI
end
