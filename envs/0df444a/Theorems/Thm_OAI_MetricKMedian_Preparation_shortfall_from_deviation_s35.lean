-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_shortfall_from_deviation_s35
-- name    : OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:37:55.642689+00:00
-- url     : https://prove2.me/theorems/40e9bcf4-5639-4465-a62a-f4e0f07c815e
-- title:
--   OAI.MetricKMedian.Preparation.shortfall_from_deviation_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset`):
--
--   ```lean
--   theorem shortfall_from_deviation_s35 (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
--       (P : T → Finset I) (y : I → ℝ) (p : T → ℝ)
--       (p' : Ω → T → ℝ)
--       (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ)
--       (F : Finset I) {g γ p₀ : ℝ}
--       (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hp₀ : 0 < p₀)
--       (hy : ∀ i, 0 ≤ y i) (hF : ∑ i ∈ F, y i=1)
--       (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
--       (hp : ∀ t, p₀ ≤ p t)
--       (hcap : ∀ ω t, p' ω t ≤ 1)
--       (hdev : ∀ t, ν.expect (fun ω => |p' ω t-p t|) ≤ γ+Real.sqrt (g*(1+γ)))
--       (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
--       (hUv : ∀ i, ν.variance (fun ω => U ω i) ≤ g*y i)
--       (hUc : ∀ i j, i ≠ j → ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j)
--       (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
--         if i ∈ P t then p' ω t*y i/p t else 0)
--       (hYv : ∀ ω a, (κ ω).variance (fun ξ => Y ω ξ a) ≤
--         g*(if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0))
--       (hYc : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => Y ω ξ a*Y ω ξ b) ≤
--         (if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0)*
--         (if b.2 ∈ P b.1 then p' ω b.1*y b.2/p b.1 else 0)) :
--       (ν.joint κ).expect (fun z => max
--         (1-(∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0)
--         ≤ Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw.variance` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.outside` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ035K016` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.physical_old_estimates_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K010
import Definitions.Def_OAIQ035K016

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

theorem shortfall_from_deviation_s35 (ν : FiniteLaw Ω) (κ : Ω → FiniteLaw Ξ)
    (P : T → Finset I) (y : I → ℝ) (p : T → ℝ)
    (p' : Ω → T → ℝ)
    (U : Ω → I → ℝ) (Y : Ω → Ξ → T × I → ℝ)
    (F : Finset I) {g γ p₀ : ℝ}
    (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hp₀ : 0 < p₀)
    (hy : ∀ i, 0 ≤ y i) (hF : ∑ i ∈ F, y i=1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (hp : ∀ t, p₀ ≤ p t)
    (hcap : ∀ ω t, p' ω t ≤ 1)
    (hdev : ∀ t, ν.expect (fun ω => |p' ω t-p t|) ≤ γ+Real.sqrt (g*(1+γ)))
    (hUm : ∀ i, ν.expect (fun ω => U ω i)=y i)
    (hUv : ∀ i, ν.variance (fun ω => U ω i) ≤ g*y i)
    (hUc : ∀ i j, i ≠ j → ν.expect (fun ω => U ω i*U ω j) ≤ y i*y j)
    (hYm : ∀ ω t i, (κ ω).expect (fun ξ => Y ω ξ (t,i))=
      if i ∈ P t then p' ω t*y i/p t else 0)
    (hYv : ∀ ω a, (κ ω).variance (fun ξ => Y ω ξ a) ≤
      g*(if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0))
    (hYc : ∀ ω a b, a ≠ b → (κ ω).expect (fun ξ => Y ω ξ a*Y ω ξ b) ≤
      (if a.2 ∈ P a.1 then p' ω a.1*y a.2/p a.1 else 0)*
      (if b.2 ∈ P b.1 then p' ω b.1*y b.2/p b.1 else 0)) :
    (ν.joint κ).expect (fun z => max
      (1-(∑ i ∈ F ∩ SupplierStars.outside P, U z.1 i)-(∑ t, ∑ i ∈ F, Y z.1 z.2 (t,i))) 0)
      ≤ Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
