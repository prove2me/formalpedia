-- Prove2me | Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_expanded_bound
-- name    : OAI.MetricKMedian.GeneratorAverage.expanded_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:23:51.195899+00:00
-- url     : https://prove2.me/theorems/dc30e412-1079-4a11-ad10-1e328aaea622
-- title:
--   OAI.MetricKMedian.GeneratorAverage.expanded_bound: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.GeneratorAverage`, with `open Analytic GraphComparison GraphMoments`):
--
--   ```lean
--   theorem expanded_bound (μ : FiniteLaw Ω) {g x y pHat b : ℝ}
--       (d N s : I → ℝ) (bH : H → ℝ)
--       (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
--       (qI : I → I → ℝ) (qE : H → I → ℝ)
--       (hg : 0 ≤ g) (hd : ∀ i, 0 ≤ d i) (hysum : ∑ _i : I, g=y)
--       (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
--       (hincoming : ∀ i, ∑ h, g*qE h i ≤ 1)
--       (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
--       (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
--       (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
--       (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t)
--       (hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
--         (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) :
--       let V := ∑ i, g*d i
--       let a := coefficient x y
--       2*x*(y-x)*moment 2 x*V+
--         μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
--           external g a (Analytic.B x) V bH d XE ω) ≤
--         unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i)
--           (GraphMoments.kernel g qE) x y pHat+Analytic.B x*g*V
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.B`, `OAI.MetricKMedian.Analytic.coefficient` and `OAI.MetricKMedian.Analytic.moment` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.FiniteLaw` and `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.GeneratorAverage.external`, `OAI.MetricKMedian.GeneratorAverage.inside` and `OAI.MetricKMedian.GraphMoments.kernel` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.GraphComparison.unnormalizedDrift` (definitions bundle `OAIQ035K021` of this split).
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
namespace MetricKMedian.GeneratorAverage
open Analytic GraphComparison GraphMoments

variable {Ω I H : Type*} [Fintype Ω] [Fintype I] [Fintype H] [DecidableEq I]

theorem expanded_bound (μ : FiniteLaw Ω) {g x y pHat b : ℝ}
    (d N s : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 ≤ g) (hd : ∀ i, 0 ≤ d i) (hysum : ∑ _i : I, g=y)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hincoming : ∀ i, ∑ h, g*qE h i ≤ 1)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t)
    (hcap : ∀ i, (∑ h, g*qE h i*bH h) ≤
      (1-y)*b+(y-∑ t, g*qI t i)*(d i+(1-pHat*s i)*N i)) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      unnormalizedDrift (fun _ => g) d N s (fun i t => qI t i)
        (GraphMoments.kernel g qE) x y pHat+Analytic.B x*g*V := by
  sorry

end MetricKMedian.GeneratorAverage
end
end

end OAI
end
