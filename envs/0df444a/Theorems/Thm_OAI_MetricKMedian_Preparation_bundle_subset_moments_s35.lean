-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_bundle_subset_moments_s35
-- name    : OAI.MetricKMedian.Preparation.bundle_subset_moments_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:34:57.267603+00:00
-- url     : https://prove2.me/theorems/bc167404-82f9-4a24-808a-8f8e5a51d041
-- title:
--   OAI.MetricKMedian.Preparation.bundle_subset_moments_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset`):
--
--   ```lean
--   theorem bundle_subset_moments_s35 (μ : FiniteLaw Ξ) (Y : Ξ → T × I → ℝ)
--       (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ) (F : Finset I) (g : ℝ)
--       (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
--       (hv : ∀ a, μ.variance (fun ξ => Y ξ a) ≤ g*(if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0))
--       (hc : ∀ a b, a ≠ b → μ.expect (fun ξ => Y ξ a*Y ξ b) ≤
--         (if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0)*
--         (if b.2 ∈ P b.1 then p' b.1*y b.2/p b.1 else 0)) :
--       μ.expect (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i))=
--         (∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) ∧
--       μ.variance (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i)) ≤
--         g*(∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ035K004` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset
variable {I T Ω Ξ : Type} [Fintype I] [DecidableEq I]
  [Fintype T] [DecidableEq T] [Fintype Ω] [Fintype Ξ]

omit [Fintype Ω] in

theorem bundle_subset_moments_s35 (μ : FiniteLaw Ξ) (Y : Ξ → T × I → ℝ)
    (P : T → Finset I) (y : I → ℝ) (p p' : T → ℝ) (F : Finset I) (g : ℝ)
    (hm : ∀ t i, μ.expect (fun ξ => Y ξ (t,i))=if i ∈ P t then p' t*y i/p t else 0)
    (hv : ∀ a, μ.variance (fun ξ => Y ξ a) ≤ g*(if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0))
    (hc : ∀ a b, a ≠ b → μ.expect (fun ξ => Y ξ a*Y ξ b) ≤
      (if a.2 ∈ P a.1 then p' a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' b.1*y b.2/p b.1 else 0)) :
    μ.expect (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i))=
      (∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) ∧
    μ.variance (fun ξ => ∑ t, ∑ i ∈ F, Y ξ (t,i)) ≤
      g*(∑ t, (∑ i ∈ F ∩ P t, y i)*p' t/p t) := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
