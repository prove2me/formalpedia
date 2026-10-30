-- Prove2me | Theorems.Thm_OAI_MetricKMedian_GraphComparison_unnormalized_drift_le
-- name    : OAI.MetricKMedian.GraphComparison.unnormalized_drift_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:24:19.40758+00:00
-- url     : https://prove2.me/theorems/944c51ff-7a47-40cb-b35d-7b5c1d716614
-- title:
--   OAI.MetricKMedian.GraphComparison.unnormalized_drift_le: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.GraphComparison`, with `open FiniteComparison Analytic`):
--
--   ```lean
--   theorem unnormalized_drift_le {I : Type*} [Fintype I]
--       {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
--       (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
--       (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
--       (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
--       (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
--       (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
--       (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
--       (he : |pHat-P x| ≤ ζ)
--       (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
--       (hK : ∀ i t, K i t ≤
--         (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
--       unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.GraphComparison.unnormalizedDrift` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.GraphComparison

open FiniteComparison Analytic

theorem unnormalized_drift_le {I : Type*} [Fintype I]
    {μ d N s : I → ℝ} {q K : I → I → ℝ} {x y pHat ζ : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hμ0 : ∀ i, 0 ≤ μ i) (hμ : ∑ i, μ i=y)
    (hd0 : ∀ i, 0 ≤ d i) (hV : 0 < ∑ i, μ i*d i) (hN : ∀ i, 0 ≤ N i)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-P x| ≤ ζ)
    (hcomp : ∀ i t, q i t < 1 → N i*(1-pHat*q i t) ≤ d i+d t)
    (hK : ∀ i t, K i t ≤
      (s i*(1-∑ u, μ u*q i u)+s t*(1-∑ u, μ u*q t u))/2) :
    unnormalizedDrift μ d N s q K x y pHat ≤ 12*ζ*(∑ i, μ i*d i) := by
  sorry

end MetricKMedian.GraphComparison
end
end

end OAI
end
