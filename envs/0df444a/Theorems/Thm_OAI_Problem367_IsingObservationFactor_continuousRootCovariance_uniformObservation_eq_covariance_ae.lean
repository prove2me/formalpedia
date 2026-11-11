-- Prove2me | Theorems.Thm_OAI_Problem367_IsingObservationFactor_continuousRootCovariance_uniformObservation_eq_covariance_ae
-- name    : OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:47:01.171683+00:00
-- url     : https://prove2.me/theorems/92f4a0b3-7c08-4131-ae83-67daa18192b0
-- title:
--   OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae` of [lean/OAI/Probability/FreeIsing/Ising/CanonicalCovariancePullback.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalCovariancePullback.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingObservationFactor`, with `open MeasureTheory ProbabilityTheory Filter`, `open scoped NNReal`, `open IsingObservationInnovation`):
--
--   ```lean
--   theorem continuousRootCovariance_uniformObservation_eq_covariance_ae
--       (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (v : TreeVertex d) (t : ℝ≥0) :
--       (fun q => continuousRootCovariance hb v t (uniformObservation q)) =ᵐ[
--         μ.prod (labelMeasure d)]
--         IsingInnovation.covariance beta (fun s u => WienerSampler.sample u s)
--           (ConnectedHull.root d) v t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingObservationInnovation.uniformObservation`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.sample` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingInnovation.covariance` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingObservationFactor.continuousRootCovariance` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex`, `OAI.Problem367.isingSpinMeasurable` and `OAI.Problem367.labelMeasure` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingObservationFactor.exists_canonical_root_covariance_integral_representation` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/CanonicalCovariancePullback.lean (declaration OAI.Problem367.IsingObservationFactor.continuousRootCovariance_uniformObservation_eq_covariance_ae)

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
open scoped NNReal

namespace Problem367.IsingObservationFactor
open IsingObservationInnovation

variable {d : ℕ} {beta : ℝ}

theorem continuousRootCovariance_uniformObservation_eq_covariance_ae
    (hd : 3 ≤ d) {μ : Measure (TreeVertex d → IsingSpin)}
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (v : TreeVertex d) (t : ℝ≥0) :
    (fun q => continuousRootCovariance hb v t (uniformObservation q)) =ᵐ[
      μ.prod (labelMeasure d)]
      IsingInnovation.covariance beta (fun s u => WienerSampler.sample u s)
        (ConnectedHull.root d) v t := by
  sorry

end Problem367.IsingObservationFactor

end

end OAI
end
