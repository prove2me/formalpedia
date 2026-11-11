-- Prove2me | Theorems.Thm_OAI_Problem367_IsingContinuousCopyCoefficients_response_eq_raw_ae
-- name    : OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:46:00.649824+00:00
-- url     : https://prove2.me/theorems/d8423be0-ebe0-4573-ae4f-a4cc028907b0
-- title:
--   OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae` of [lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367.IsingContinuousCopyCoefficients`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped NNReal Topology`, `open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy`):
--
--   ```lean
--   lemma response_eq_raw_ae (hd : 3 ≤ d)
--       (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
--       (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
--       (j : Bool) (v : TreeVertex d) (t : ℝ≥0) :
--       response hb j v t =ᵐ[copies beta μ] fun q =>
--         infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => projection j q i t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.infiniteGibbsResponse`, `OAI.Problem367.ConnectedHull.root`, `OAI.Problem367.IsingObservationFactor.copies`, `OAI.Problem367.IsingObservationInnovation.Paths`, `OAI.Problem367.WienerSampler.Path` and `OAI.Problem367.WienerSampler.pathMeasurableSpace` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingCopyEnergy.projection` (definitions bundle `Q243FI004` of this split); `OAI.Problem367.IsingContinuousCopyCoefficients.response` (definitions bundle `Q243FI005` of this split); `OAI.Problem367.HasFreeIsingLaw`, `OAI.Problem367.IsingSpin`, `OAI.Problem367.TreeVertex` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proof of `OAI.Problem367.IsingContinuousCopyCoefficients.response_row_energy` of this split imports it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Ising/ContinuousCopyCoefficients.lean (declaration OAI.Problem367.IsingContinuousCopyCoefficients.response_eq_raw_ae)

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
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology

namespace Problem367.IsingContinuousCopyCoefficients
open IsingObservationInnovation IsingObservationFactor IsingCopyEnergy

variable {d : ℕ} {beta : ℝ}

variable {μ : Measure (TreeVertex d → IsingSpin)} [IsProbabilityMeasure μ]

lemma response_eq_raw_ae (hd : 3 ≤ d)
    (hμ : HasFreeIsingLaw (Real.tanh beta) μ) (hb : 0 ≤ beta)
    (hcrit : ((d - 1 : ℕ) : ℝ) * Real.tanh beta ^ 2 ≤ 1)
    (j : Bool) (v : TreeVertex d) (t : ℝ≥0) :
    response hb j v t =ᵐ[copies beta μ] fun q =>
      infiniteGibbsResponse beta (ConnectedHull.root d) v (fun i => projection j q i t) := by
  sorry

end Problem367.IsingContinuousCopyCoefficients

end

end OAI
end
