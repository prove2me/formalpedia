-- Prove2me | Theorems.Thm_OAI_Problem367_FiniteIsingFiltering_mean_compensatedSquare_martingale
-- name    : OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:56.790127+00:00
-- url     : https://prove2.me/theorems/bb61b24e-67b3-4a39-b1bd-c78a7389ff09
-- title:
--   OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale` of [lean/OAI/Probability/FreeIsing/Estimates/FiniteIsingCompensatedSquare.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/FiniteIsingCompensatedSquare.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.FiniteIsingFiltering`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal ENNReal Topology BigOperators`):
--
--   ```lean
--   theorem mean_compensatedSquare_martingale
--       {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
--       (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
--       (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
--       (hmB : ∀ i t, Measurable (B i t))
--       (hcB : ∀ i omega, Continuous (fun t => B i t omega))
--       (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
--       Martingale (fun t p => mean beta D v B t p ^ 2 - quadraticCompensator beta D v B t p)
--         (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.FiniteIsingFiltering.State`, `OAI.Problem367.FiniteIsingFiltering.mean`, `OAI.Problem367.FiniteIsingFiltering.observationFiltration` and `OAI.Problem367.FiniteIsingFiltering.quadraticCompensator` (definitions bundle `Q243FI003` of this split); `OAI.Problem367.ConnectedFinset`, `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_compensatedSquare_martingale` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Estimates/FiniteIsingCompensatedSquare.lean (declaration OAI.Problem367.FiniteIsingFiltering.mean_compensatedSquare_martingale)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI003

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace Problem367.FiniteIsingFiltering

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem mean_compensatedSquare_martingale
    {beta : ℝ} {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ)
    (ν : TreeVertex d → Measure Ω) {B : TreeVertex d → ℝ≥0 → Ω → ℝ}
    (hB : ∀ i, IsPreBrownianReal (B i) (ν i))
    (hmB : ∀ i t, Measurable (B i t))
    (hcB : ∀ i omega, Continuous (fun t => B i t omega))
    (D : Finset (TreeVertex d)) (hD : ConnectedFinset D) (v : D) :
    Martingale (fun t p => mean beta D v B t p ^ 2 - quadraticCompensator beta D v B t p)
      (observationFiltration B hmB D) (μ.prod (Measure.infinitePi ν)) := by
  sorry

end Problem367.FiniteIsingFiltering

end

end OAI
end
