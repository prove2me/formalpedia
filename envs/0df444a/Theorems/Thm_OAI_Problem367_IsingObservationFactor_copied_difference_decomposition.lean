-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_copied_difference_decomposition
-- name    : OAI.Problem367.IsingObservationFactor.copied_difference_decomposition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:15.057756+00:00
-- url     : https://prove2.me/theorems/a3d869a4-47dd-4584-b6ad-d0e8e65638b0
-- title:
--   OAI.Problem367.IsingObservationFactor.copied_difference_decomposition: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.copied_difference_decomposition` of [lean/OAI/Probability/FreeIsing/Ising/CopiedDriftDecomposition.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopiedDriftDecomposition.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal`, `open IsingObservationInnovation IsingCopyEnergy`):
--
--   ```lean
--   theorem copied_difference_decomposition
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d)
--       {Y : ℝ≥0 → Paths d → ℝ} {Z : Bool → ℝ≥0 → Joint d → ℝ}
--       (hfield : ∀ᵐ x ∂observationLaw μ, ∀ t,
--         continuousField beta v t x = Y t x +
--           nnrealTimePrimitive (canonicalResponseDrift beta v) t x)
--       (hcopy : ∀ j, ∀ᵐ z ∂copies beta μ, ∀ t,
--         Y t (projection j z) = Z j t z) :
--       ∀ᵐ z ∂copies beta μ, ∀ t,
--         continuousDifference beta v t z = (Z true t z - Z false t z) +
--           nnrealTimePrimitive (copyResponseDriftDifference beta v) t z
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.nnrealTimePrimitive`, `OAI.Problem367.IsingCopyEnergy.Joint`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyEnergy.projection` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingObservationFactor.canonicalResponseDrift`, `OAI.Problem367.IsingObservationFactor.continuousDifference`, `OAI.Problem367.IsingObservationFactor.continuousField` and `OAI.Problem367.IsingObservationFactor.copyResponseDriftDifference` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.actual_variance_analysis` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CopiedDriftDecomposition.lean (declaration OAI.Problem367.IsingObservationFactor.copied_difference_decomposition)

import Mathlib
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Marginal
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

attribute [-instance] _root_.OAI.Problem367.TreeKoopman.labelProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem copied_difference_decomposition
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta) (v : TreeVertex d)
    {Y : ℝ≥0 → Paths d → ℝ} {Z : Bool → ℝ≥0 → Joint d → ℝ}
    (hfield : ∀ᵐ x ∂observationLaw μ, ∀ t,
      continuousField beta v t x = Y t x +
        nnrealTimePrimitive (canonicalResponseDrift beta v) t x)
    (hcopy : ∀ j, ∀ᵐ z ∂copies beta μ, ∀ t,
      Y t (projection j z) = Z j t z) :
    ∀ᵐ z ∂copies beta μ, ∀ t,
      continuousDifference beta v t z = (Z true t z - Z false t z) +
        nnrealTimePrimitive (copyResponseDriftDifference beta v) t z := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
