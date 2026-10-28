-- Prove2me | Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_averaged_ideal_drift
-- name    : OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:19:08.564832+00:00
-- url     : https://prove2.me/theorems/785763f4-b2b5-4508-9532-a4ed8105d3a5
-- title:
--   OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.GeneratorAverage`, with `open Analytic GraphComparison GraphMoments`):
--
--   ```lean
--   theorem averaged_ideal_drift (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
--       (d N : I → ℝ) (bH : H → ℝ)
--       (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
--       (qI : I → I → ℝ) (qE : H → I → ℝ)
--       (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
--       (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
--       (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
--       (hqI0 : ∀ h i, 0 ≤ qI h i) (hqI : ∀ h i, qI h i ≤ 1)
--       (hqE0 : ∀ h i, 0 ≤ qE h i) (hqE : ∀ h i, qE h i ≤ 1)
--       (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
--       (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
--       (he : |pHat-Analytic.P x| ≤ ζ)
--       (hcomp : ∀ i t, qI t i < 1 → N i*(1-pHat*qI t i) ≤ d i+d t)
--       (hb : ∀ h, bH h ≤ b)
--       (htaper : ∀ h i, 0 < qE h i → bH h ≤ d i+(1-pHat*qE h i)*N i)
--       (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
--       (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
--       (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
--       (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t) :
--       let V := ∑ i, g*d i
--       let a := coefficient x y
--       2*x*(y-x)*moment 2 x*V+
--         μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
--           external g a (Analytic.B x) V bH d XE ω) ≤
--         Analytic.B x*g*V+12*ζ*V
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.B`, `OAI.MetricKMedian.Analytic.P`, `OAI.MetricKMedian.Analytic.coefficient` and `OAI.MetricKMedian.Analytic.moment` (definitions bundle `OAIQ035K000` of this split); `OAI.MetricKMedian.FiniteLaw` and `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.GeneratorAverage.external` and `OAI.MetricKMedian.GeneratorAverage.inside` (definitions bundle `OAIQ035K008` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Taper.GraphData.drift` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K000
import Definitions.Def_OAIQ035K004
import Definitions.Def_OAIQ035K008

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

theorem averaged_ideal_drift (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
    (d N : I → ℝ) (bH : H → ℝ)
    (XI : Ω → I → I → ℝ) (XE : Ω → H → I → ℝ)
    (qI : I → I → ℝ) (qE : H → I → ℝ)
    (hg : 0 < g) (hx0 : 0 ≤ x) (hx : x ≤ 1)
    (hysum : ∑ _i : I, g=y) (hy : y ≤ 1)
    (hd : ∀ i, 0 ≤ d i) (hN : ∀ i, 0 ≤ N i)
    (hqI0 : ∀ h i, 0 ≤ qI h i) (hqI : ∀ h i, qI h i ≤ 1)
    (hqE0 : ∀ h i, 0 ≤ qE h i) (hqE : ∀ h i, qE h i ≤ 1)
    (hmass : ∀ i, (∑ h, g*qE h i)=1-∑ t, g*qI t i)
    (hp0 : 0 ≤ pHat) (hp : pHat ≤ 1/2) (hζ0 : 0 ≤ ζ) (hζ : ζ < 1/4)
    (he : |pHat-Analytic.P x| ≤ ζ)
    (hcomp : ∀ i t, qI t i < 1 → N i*(1-pHat*qI t i) ≤ d i+d t)
    (hb : ∀ h, bH h ≤ b)
    (htaper : ∀ h i, 0 < qE h i → bH h ≤ d i+(1-pHat*qE h i)*N i)
    (hfirstI : ∀ h i, μ.expect (fun ω => XI ω h i)=qI h i)
    (hfirstE : ∀ h i, μ.expect (fun ω => XE ω h i)=qE h i)
    (hidem : ∀ ω h i, XE ω h i*XE ω h i=XE ω h i)
    (hpair : ∀ h i t, i ≠ t → μ.expect (fun ω => XE ω h i*XE ω h t)=qE h i*qE h t) :
    let V := ∑ i, g*d i
    let a := coefficient x y
    2*x*(y-x)*moment 2 x*V+
      μ.expect (fun ω => inside g a (a*V+(1-y)*b) d XI ω+
        external g a (Analytic.B x) V bH d XE ω) ≤
      Analytic.B x*g*V+12*ζ*V := by
  sorry

end MetricKMedian.GeneratorAverage
end
end

end OAI
end
