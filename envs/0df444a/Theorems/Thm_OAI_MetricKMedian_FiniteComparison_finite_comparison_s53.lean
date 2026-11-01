-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FiniteComparison_finite_comparison_s53
-- name    : OAI.MetricKMedian.FiniteComparison.finite_comparison_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:32:08.292068+00:00
-- url     : https://prove2.me/theorems/77dd904b-b81b-4afb-807e-42044f1d89dd
-- title:
--   OAI.MetricKMedian.FiniteComparison.finite_comparison_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FiniteComparison.finite_comparison` of [lean/OAI/Combinatorics/KMedian/Analysis/FiniteComparison.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteComparison.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FiniteComparison`, with `open Analytic`):
--
--   ```lean
--   theorem finite_comparison_s53 {I : Type*} [Fintype I] {π D R : I → ℝ}
--       {q : I → I → ℝ} {s : I → ℝ} {x y : ℝ}
--       (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
--       (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
--       (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1) (_hR0 : ∀ i, 0 ≤ R i)
--       (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
--       (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
--       (hcomp : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t) :
--       average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
--         2*(P x*(y-x)^2/y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.P` and `OAI.MetricKMedian.Analytic.m` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.FiniteComparison.average` and `OAI.MetricKMedian.FiniteComparison.rawRow` (definitions bundle `OAIQ053K006` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.GeneratorAverage.averaged_ideal_drift_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Analysis/FiniteComparison.lean (declaration OAI.MetricKMedian.FiniteComparison.finite_comparison)

import Mathlib
import Definitions.Def_OAIQ053K000
import Definitions.Def_OAIQ053K006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FiniteComparison

open Analytic

theorem finite_comparison_s53 {I : Type*} [Fintype I] {π D R : I → ℝ}
    {q : I → I → ℝ} {s : I → ℝ} {x y : ℝ}
    (hx0 : 0 ≤ x) (hx : x ≤ 1) (hy0 : 0 < y) (hy : y ≤ 1)
    (hπ0 : ∀ i, 0 ≤ π i) (hπ : ∑ i, π i = 1)
    (hD0 : ∀ i, 0 ≤ D i) (hD : average π D = 1) (_hR0 : ∀ i, 0 ≤ R i)
    (hq0 : ∀ i t, 0 ≤ q i t) (hq : ∀ i t, q i t ≤ 1)
    (hs0 : ∀ i, 0 ≤ s i) (hs : ∀ i, s i ≤ 1)
    (hcomp : ∀ i t, q i t < 1 → R i*(1-P x*q i t) ≤ D i+D t) :
    average π (fun i => rawRow π D (q i) (P x) (m x) y (s i) (D i) (R i)) ≤
      2*(P x*(y-x)^2/y) := by
  sorry

end MetricKMedian.FiniteComparison

end
end

end OAI
end
