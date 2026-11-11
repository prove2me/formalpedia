-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_variance_analysis_of_joined_decomposition
-- name    : OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:42.313199+00:00
-- url     : https://prove2.me/theorems/9061d9d8-8fea-427f-9643-54700d07ee7f
-- title:
--   OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition` of [lean/OAI/Probability/FreeIsing/Ising/ActualVarianceAnalysis.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ActualVarianceAnalysis.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open IsingObservationInnovation IsingCopyEnergy`):
--
--   ```lean
--   theorem variance_analysis_of_joined_decomposition
--       (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (S : IsingJoinedResponseIntegrals.IntegralSystem hb μ)
--       (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
--         continuousDifference beta (ConnectedHull.root d) t z =
--           (S.total true t z - S.total false t z) +
--             nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
--       (T : ℝ≥0) :
--       AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
--         (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
--           field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
--       (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
--         deriv (fun s : ℝ => ∫ z,
--           (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
--             field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
--           ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive`, `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingCopyEnergy.density`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationFactor.field`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingJoinedResponseIntegrals.IntegralSystem`, `OAI.Problem367.IsingObservationFactor.continuousDifference` and `OAI.Problem367.IsingObservationFactor.copyResponseDriftDifference` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.actual_variance_analysis` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ActualVarianceAnalysis.lean (declaration OAI.Problem367.IsingObservationFactor.variance_analysis_of_joined_decomposition)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem variance_analysis_of_joined_decomposition
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (S : IsingJoinedResponseIntegrals.IntegralSystem hb μ)
    (hrep : ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta (ConnectedHull.root d) t z =
        (S.total true t z - S.total false t z) +
          nnrealTimePrimitive (copyResponseDriftDifference beta (ConnectedHull.root d)) t z)
    (T : ℝ≥0) :
    AbsolutelyContinuousOnInterval (fun t : ℝ => ∫ z,
      (field beta (ConnectedHull.root d) t.toNNReal z.2.1 -
        field beta (ConnectedHull.root d) t.toNNReal z.2.2) ^ 2 ∂copies beta μ) 0 T ∧
    (∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) T),
      deriv (fun s : ℝ => ∫ z,
        (field beta (ConnectedHull.root d) s.toNNReal z.2.1 -
          field beta (ConnectedHull.root d) s.toNNReal z.2.2) ^ 2 ∂copies beta μ) t =
        ∫ z, density beta (ConnectedHull.root d) t z ∂copies beta μ) := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
