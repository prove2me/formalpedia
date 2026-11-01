-- Prove2me | Theorems.Thm_OAI_MetricKMedian_GeneratorAverage_averaged_ideal_drift_s53
-- name    : OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:32:08.89968+00:00
-- url     : https://prove2.me/theorems/fd7e2470-624d-4898-a3e1-7ebe00df4b58
-- title:
--   OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift` of [lean/OAI/Combinatorics/KMedian/Process/AveragedGenerator.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/AveragedGenerator.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.GeneratorAverage`, with `open Analytic GraphComparison GraphMoments`):
--
--   ```lean
--   theorem averaged_ideal_drift_s53 (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
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
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.B`, `OAI.MetricKMedian.Analytic.P`, `OAI.MetricKMedian.Analytic.coefficient` and `OAI.MetricKMedian.Analytic.moment` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.FiniteLaw` and `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.GeneratorAverage.external` and `OAI.MetricKMedian.GeneratorAverage.inside` (definitions bundle `OAIQ053K007` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalPhysicalKernel.step_drift_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/AveragedGenerator.lean (declaration OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift)

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K004
import Definitions.Def_OAIQ053K007

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

theorem averaged_ideal_drift_s53 (μ : FiniteLaw Ω) {g x y pHat ζ b : ℝ}
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
