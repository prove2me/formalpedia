-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_exists_canonical_root_covariance_integral_representation
-- name    : OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:38.559531+00:00
-- url     : https://prove2.me/theorems/c0707d3d-118d-4707-b656-b57936909feb
-- title:
--   OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalIntegralRepresentation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalIntegralRepresentation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal Topology`, `open IsingObservationInnovation`):
--
--   ```lean
--   theorem exists_canonical_root_covariance_integral_representation
--       (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
--       ∃ (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
--         (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ)),
--         (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
--         (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
--         (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
--         (∀ w, J w 0 =ᵐ[observationLaw μ] 0) ∧
--         (∀ w t, (∫ x, J w t x ∂observationLaw μ) = 0) ∧
--         (∀ w t, (∫ x, J w t x ^ 2 ∂observationLaw μ) =
--           ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
--             continuousRootCovariance hb w s.toNNReal x ^ 2 ∂observationLaw μ) ∧
--         (∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
--           Tendsto (fun n => ∫ x,
--             (BrownianIntegralProcess.stoppedUniformSum
--               (fun s x => innovationMap beta x w s)
--               (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
--               ∂observationLaw μ) atTop (𝓝 0)) ∧
--         (∀ t, HasSum (fun w => (hJ2 w t).toLp (J w t))
--           ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
--             (posterior beta (ConnectedHull.root d) t)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.IsingObservationInnovation.filtration`, `OAI.Problem367.IsingObservationInnovation.innovationMap`, `OAI.Problem367.IsingObservationInnovation.observationLaw`, `OAI.Problem367.IsingObservationInnovation.posterior`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.BrownianIntegralProcess.stoppedUniformSum` (definitions bundle `Q243FI001` of this split); `OAI.Problem367.IsingObservationInnovation.posterior_memLp` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingObservationFactor.continuousRootCovariance` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.canonical_field_eq_normalized_integral` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalIntegralRepresentation.lean (declaration OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation)

import Mathlib
import Mathlib.MeasureTheory.Integral.Marginal
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI005

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}
variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

theorem exists_canonical_root_covariance_integral_representation
    (hd : 3 ≤ d) (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1) :
    ∃ (J : TreeVertex d → ℝ≥0 → Paths d → ℝ)
      (hJ2 : ∀ w t, MemLp (J w t) 2 (observationLaw μ)),
      (∀ w, IsStronglyPredictable (filtration d) (J w)) ∧
      (∀ w, Martingale (J w) (filtration d) (observationLaw μ)) ∧
      (∀ w, ∀ᵐ x ∂observationLaw μ, Continuous (fun t => J w t x)) ∧
      (∀ w, J w 0 =ᵐ[observationLaw μ] 0) ∧
      (∀ w t, (∫ x, J w t x ∂observationLaw μ) = 0) ∧
      (∀ w t, (∫ x, J w t x ^ 2 ∂observationLaw μ) =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ x,
          continuousRootCovariance hb w s.toNNReal x ^ 2 ∂observationLaw μ) ∧
      (∀ w (N : ℕ), 0 < N → ∀ t ≤ (N : ℝ≥0),
        Tendsto (fun n => ∫ x,
          (BrownianIntegralProcess.stoppedUniformSum
            (fun s x => innovationMap beta x w s)
            (continuousRootCovariance hb w) N n t x - J w t x) ^ 2
            ∂observationLaw μ) atTop (𝓝 0)) ∧
      (∀ t, HasSum (fun w => (hJ2 w t).toLp (J w t))
        ((posterior_memLp beta μ (ConnectedHull.root d) t 2).toLp
          (posterior beta (ConnectedHull.root d) t))) := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
