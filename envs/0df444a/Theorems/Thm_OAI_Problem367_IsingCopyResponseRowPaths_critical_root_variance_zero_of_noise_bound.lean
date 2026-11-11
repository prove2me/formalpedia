-- Prove2me | Theorems.Thm_OAI_Problem367_IsingCopyResponseRowPaths_critical_root_variance_zero_of_noise_bound
-- name    : OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:42:37.6742+00:00
-- url     : https://prove2.me/theorems/59e13d91-8076-4651-a79b-7ee9413b3ede
-- title:
--   OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound` of [lean/OAI/Probability/FreeIsing/Ising/CriticalSpatialRecovery.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CriticalSpatialRecovery.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingCopyResponseRowPaths`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped NNReal`, `open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss`, `open ConnectedHull`):
--
--   ```lean
--   theorem critical_root_variance_zero_of_noise_bound
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
--       (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
--       (u w : TreeVertex d) (huw : treeAdj u w)
--       {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
--       (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
--       (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
--         ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
--           noiseEnergy (μ := μ) hb t v ≤
--             B * logVariance hb μ u w t *
--               ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
--             E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
--       (hAC : AbsolutelyContinuousOnInterval
--         (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
--       (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
--         deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
--           ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
--       ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingCopySmallLogLoss.siteVariance`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyResponseRowPaths.noiseEnergy` and `OAI.Problem367.IsingCopySmallLogLoss.logVariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex`, `OAI.Problem367.isingSpinMeasurable` and `OAI.Problem367.treeAdj` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.free_ising_factor_below_threshold_of_actual_variance_identity` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CriticalSpatialRecovery.lean (declaration OAI.Problem367.IsingCopyResponseRowPaths.critical_root_variance_zero_of_noise_bound)

import Mathlib
import Mathlib.MeasureTheory.Function.FactorsThrough
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
open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace Problem367.IsingCopyResponseRowPaths
open IsingObservationFactor IsingCopySmallLogLoss IsingCriticalSmallLogLoss
open ConnectedHull

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem critical_root_variance_zero_of_noise_bound
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hd : 3 ≤ d) (hb : 0 ≤ beta)
    (hcritical : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 = 1) (T : ℝ≥0)
    (u w : TreeVertex d) (huw : treeAdj u w)
    {B E c a q C₀ : ℝ} (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hc : 0 < c) (ha : 0 < a) (hq : 1 < q)
    (hnoise : ∀ (t : ℝ≥0), 0 < t → t ≤ T → ∀ (u w : TreeVertex d), treeAdj u w →
      ∀ v : TreeVertex d, C₀ / min (Real.sqrt (t : ℝ)) 1 ≤ (v.1.length : ℝ) →
        noiseEnergy (μ := μ) hb t v ≤
          B * logVariance hb μ u w t *
            ((v.1.length : ℝ) * Real.exp (-(c * min (Real.sqrt (t : ℝ)) 1) * v.1.length)) +
          E * ((v.1.length : ℝ) ^ 2 * Real.exp (-a * q ^ v.1.length)))
    (hAC : AbsolutelyContinuousOnInterval
      (fun s : ℝ => siteVariance beta μ (root d) s.toNNReal) 0 (T : ℝ))
    (hderiv : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) (T : ℝ)),
      deriv (fun r : ℝ => siteVariance beta μ (root d) r.toNNReal) s =
        ∫ z, IsingCopyEnergy.density beta (root d) s z ∂copies beta μ) :
    ∀ t : ℝ≥0, t ≤ T → siteVariance beta μ (root d) t = 0 := by
  sorry

end Problem367.IsingCopyResponseRowPaths

end

end OAI
end
