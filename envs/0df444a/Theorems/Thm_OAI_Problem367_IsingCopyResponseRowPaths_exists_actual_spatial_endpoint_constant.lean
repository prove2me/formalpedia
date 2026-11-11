-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_exists_actual_spatial_endpoint_constant
-- name    : OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:32.55965+00:00
-- url     : https://prove2.me/theorems/1685c0aa-c7dd-4d9c-a6e9-06404fcf65b9
-- title:
--   OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant` of [lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyResponseRowPaths`, with `open MeasureTheory ProbabilityTheory`, `open scoped NNReal`, `open IsingObservationInnovation IsingObservationFactor IsingCopySpectral`, `open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull`):
--
--   ```lean
--   theorem exists_actual_spatial_endpoint_constant
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
--       (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1))
--       {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
--       (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
--       ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → 0 < t →
--         let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
--         let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
--         ∀ (K ω : ℝ), 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
--         (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
--           noiseEnergy (μ := μ) hb t v ≤ B * S *
--             ((v.1.length : ℝ) * Real.exp (-(c * ω) * v.1.length)) +
--             E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) →
--         (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
--           linearEnergy (μ := μ) hb t v ≤ B * V * Real.exp (-(c * ω) * v.1.length) +
--             E * Real.exp (-a * q ^ v.1.length)) →
--         CriticalSpatialEndpointBounds
--           (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
--           (∑' n, noiseShellEnergy (μ := μ) hb t n)
--           (∑' n, linearShellEnergy (μ := μ) hb t n)
--           (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n)) S V M K ω
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingConditionalCopyBounds.fieldDifference`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.CriticalSpatialEndpointBounds` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingCopyResponseRowPaths.linearEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.linearShellEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.noiseEnergy`, `OAI.Problem367.IsingCopyResponseRowPaths.noiseShellEnergy` and `OAI.Problem367.IsingCopySpectral.cavityLogDifference` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex`, `OAI.Problem367.isingSpinMeasurable` and `OAI.Problem367.treeAdj` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopySpatialEndpoints.lean (declaration OAI.Problem367.IsingCopyResponseRowPaths.exists_actual_spatial_endpoint_constant)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationInnovation IsingObservationFactor IsingCopySpectral
open IsingCopyStationarity IsingConditionalCopyBounds ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_actual_spatial_endpoint_constant
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcrit : Real.tanh beta ≤ 1 / Real.sqrt ((d : ℝ) - 1))
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ (t : ℝ≥0) (u w : TreeVertex d), treeAdj u w → 0 < t →
      let S := ∫ z, (cavityLogDifference hb t u w z) ^ 2 ∂copies beta μ
      let V := ∫ z, (fieldDifference beta (root d) t z) ^ 2 ∂copies beta μ
      ∀ (K ω : ℝ), 0 < V → V ≤ K → 1 ≤ K → 0 < ω → ω ≤ 1 →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤ B * S *
          ((v.1.length : ℝ) * Real.exp (-(c * ω) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length))) →
      (∀ v : TreeVertex d, C₀ / ω ≤ (v.1.length : ℝ) →
        linearEnergy (μ := μ) hb t v ≤ B * V * Real.exp (-(c * ω) * v.1.length) +
          E * Real.exp (-a * q ^ v.1.length)) →
      CriticalSpatialEndpointBounds
        (∫ z, IsingCopyEnergy.density beta (root d) t z ∂copies beta μ)
        (∑' n, noiseShellEnergy (μ := μ) hb t n)
        (∑' n, linearShellEnergy (μ := μ) hb t n)
        (∑' n, Real.sqrt (noiseShellEnergy (μ := μ) hb t n)) S V M K ω := by
  sorry

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end
