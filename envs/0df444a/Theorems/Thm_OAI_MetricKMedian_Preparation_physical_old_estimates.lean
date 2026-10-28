-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_physical_old_estimates
-- name    : OAI.MetricKMedian.Preparation.physical_old_estimates
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-27T08:28:18.139902+00:00
-- url     : https://prove2.me/theorems/7d5202e4-d877-486c-9e58-1a971b7c3b77
-- title:
--   OAI.MetricKMedian.Preparation.physical_old_estimates: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem physical_old_estimates {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
--       {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
--       (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
--       (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
--       (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
--       (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
--       (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
--       (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
--         Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
--       (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
--         (∑ i ∈ F, y i*d i)/p₀
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.expect` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.flag` (definitions bundle `OAIQ035K024` of this split); `OAI.MetricKMedian.Preparation.CoupledLaw` (definitions bundle `OAIQ035K025` of this split); `OAI.MetricKMedian.Preparation.oldAssignment` (definitions bundle `OAIQ035K036` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.nearby_assignments` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

theorem physical_old_estimates {P A : T → Finset I} {y : I → ℝ} {p c : T → ℝ}
    {g γ B p₀ : ℝ} {Δ : ℕ} (hg : 0 ≤ g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (hy : ∀ i, 0 ≤ y i) (hp₀ : 0 < p₀) (hp₀1 : p₀ ≤ 1) (hp : ∀ t, p₀ ≤ p t)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    (hP : Pairwise (fun s t => Disjoint (P s) (P t)))
    (F : Finset I) (hF : ∑ i ∈ F, y i=1) (d : I → ℝ) (hd : ∀ i, 0 ≤ d i) :
    (L.ν.joint L.κ).expect (fun z => max (1-∑ a, oldAssignment L F z a) 0) ≤
      Real.sqrt g+Real.sqrt (g/p₀)+(γ+Real.sqrt (g*(1+γ)))/p₀ ∧
    (L.ν.joint L.κ).expect (fun z => ∑ a, oldAssignment L F z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ F, y i*d i)/p₀ := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
