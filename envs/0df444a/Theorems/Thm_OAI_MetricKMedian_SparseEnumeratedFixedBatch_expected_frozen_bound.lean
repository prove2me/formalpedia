-- Prove2me | Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedFixedBatch_expected_frozen_bound
-- name    : OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:32:45.48725+00:00
-- url     : https://prove2.me/theorems/5c5e4503-6306-4c12-b96c-49871d5f1b9e
-- title:
--   OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.SparseEnumeratedFixedBatch`, with `open Finset PhysicalPotential Analytic FixedBatch`):
--
--   ```lean
--   theorem expected_frozen_bound (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
--       (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
--       (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
--       (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
--       (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
--       (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
--       {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
--       (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
--       (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
--       (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
--       (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
--       (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
--         (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
--         ((p:ℝ)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
--           ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
--           2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FixedBatch.Actions` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FixedBatch.charge`, `OAI.MetricKMedian.FixedBatch.nextAlive`, `OAI.MetricKMedian.FixedBatch.nextCap` and `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_step_bound` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I E : Type} [DecidableEq I] [DecidableEq E] [Fintype E] {n : ℕ}

theorem expected_frozen_bound (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
      ((p:ℝ)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2 := by
  sorry

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end
