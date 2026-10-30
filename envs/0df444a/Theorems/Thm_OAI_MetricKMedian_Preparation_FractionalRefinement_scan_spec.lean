-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_FractionalRefinement_scan_spec
-- name    : OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:38:00.167726+00:00
-- url     : https://prove2.me/theorems/0895c648-132f-4abd-812d-17baae2d97a8
-- title:
--   OAI.MetricKMedian.Preparation.FractionalRefinement.scan_spec: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation.FractionalRefinement`, with `open Finset`):
--
--   ```lean
--   theorem scan_spec (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
--       (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
--       ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
--         O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
--           ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.TruncatedLP.FractionalData`, `OAI.MetricKMedian.TruncatedLP.FractionalData.Valid` and `OAI.MetricKMedian.TruncatedLP.FractionalData.value` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.Preparation.RationalAllParameters` (definitions bundle `OAIQ035K033` of this split); `OAI.MetricKMedian.Preparation.FractionalRefinement.scan` (definitions bundle `OAIQ035K062` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Instance.computedPseudo_spec` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K062

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.FractionalRefinement
open Finset
variable {f j : ℕ} {X : Type} [PseudoMetricSpace X]
variable (a : TruncatedLP.FractionalData f j) (k : ℕ) (ha : a.Valid k) (hj : 0<j)
    (dc : Fin j → Fin f → ℚ) (dd : Fin j → Fin j → ℚ) (df : Fin f → Fin f → ℚ)
    (hdc : ∀ c i, 0≤dc c i) (hdd : ∀ c, dd c c=0) (hds : ∀ c c', dd c c'=dd c' c)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ b b', dist (i b) (i b')=(df b b':ℝ))
    (hc : ∀ c b, dist (client c) (i b)=(dc c b:ℝ))
    (hcc : ∀ c c', dist (client c) (client c')=(dd c c':ℝ))
    {η τ : ℝ} (p : RationalAllParameters η τ)

theorem scan_spec (hη : 0≤η) (hτ0 : 0<τ) (hτ : τ<1) (C : ℕ)
    (hC : 1+3*(p.round.g:ℝ)+(p.round.allowance:ℝ)≤(C:ℝ)) :
    ∃ O : Finset (Fin f), scan a k ha hj dc dd df hdc hdd hds i client hdf hc hcc p (k+C)=some O ∧
      O.Nonempty ∧ O.card≤k+C ∧ (Completion.Rational.score dc O:ℝ) ≤
        ((1+2/Real.exp 1+τ)/(1-τ))*(1+η)*(a.value dc:ℝ) := by
  sorry

end MetricKMedian.Preparation.FractionalRefinement
end

end OAI
end
