-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_supplier_assignments_s35
-- name    : OAI.MetricKMedian.Preparation.supplier_assignments_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:38:01.664993+00:00
-- url     : https://prove2.me/theorems/8c14ce93-93d3-49cf-854f-11bb08676372
-- title:
--   OAI.MetricKMedian.Preparation.supplier_assignments_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem supplier_assignments_s35 (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
--       {g γ B : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
--       (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
--       (next : T → T) (hnext : ∀ t, next t=t → c t=0)
--       (hAP : ∀ t, Disjoint (A t) (P t)) (s : T) (d : I → ℝ) (R : Star I T → ℝ)
--       (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp : 0 < p s) (hR0 : ∀ e, 0 ≤ R e)
--       (hradius : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
--         ∀ e, 0 < L.R ω s e → match supplier next e with
--         | .inl i => d i ≤ R e
--         | .inr t => ∀ i, 0 < L.C ω ξ (t,i) → d i ≤ R e) :
--       letI := L.finite
--       ∃ r : (L.Ω × (T → Finset I)) → (I ⊕ (T × I)) → ℝ,
--         (∀ z, 0 < (L.ν.joint L.κ).weight z →
--           (∀ a, 0 ≤ r z a ∧ r z a ≤ Sum.elim
--             (fun i => g*(L.O z.1 (.inl i):ℝ))
--             (fun ti => g*(L.C z.1 z.2 ti:ℝ)) a) ∧ (∑ a, r z a)=1) ∧
--         (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
--         (∑ i ∈ P s, y i*d i)/p s+
--           (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*R e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.flag` (definitions bundle `OAIQ035K024` of this split); `OAI.MetricKMedian.Preparation.CoupledLaw` and `OAI.MetricKMedian.Preparation.SupplierStars.supplier` (definitions bundle `OAIQ035K025` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.distant_assignments_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K024
import Definitions.Def_OAIQ035K025

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

theorem supplier_assignments_s35 (P A : T → Finset I) (y : I → ℝ) (p c : T → ℝ)
    {g γ B : ℝ} {Δ : ℕ} (hg : 0 < g) (hunit : g*(Δ:ℝ)=1)
    (L : CoupledLaw (targets A) flag (weight y P A c γ) P y p c g γ B Δ)
    (next : T → T) (hnext : ∀ t, next t=t → c t=0)
    (hAP : ∀ t, Disjoint (A t) (P t)) (s : T) (d : I → ℝ) (R : Star I T → ℝ)
    (hy : ∀ i, 0 ≤ y i) (hd : ∀ i, 0 ≤ d i) (hp : 0 < p s) (hR0 : ∀ e, 0 ≤ R e)
    (hradius : ∀ ω, 0 < L.ν.weight ω → ∀ ξ, 0 < (L.κ ω).weight ξ →
      ∀ e, 0 < L.R ω s e → match supplier next e with
      | .inl i => d i ≤ R e
      | .inr t => ∀ i, 0 < L.C ω ξ (t,i) → d i ≤ R e) :
    letI := L.finite
    ∃ r : (L.Ω × (T → Finset I)) → (I ⊕ (T × I)) → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ Sum.elim
          (fun i => g*(L.O z.1 (.inl i):ℝ))
          (fun ti => g*(L.C z.1 z.2 ti:ℝ)) a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*(Sum.elim d (fun ti => d ti.2) a)) ≤
      (∑ i ∈ P s, y i*d i)/p s+
        (∑ e, (if s ∈ targets A e then weight y P A c γ e else 0)*R e) := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
