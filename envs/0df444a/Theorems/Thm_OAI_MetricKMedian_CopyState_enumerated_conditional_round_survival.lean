-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_enumerated_conditional_round_survival
-- name    : OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:29:24.213979+00:00
-- url     : https://prove2.me/theorems/65e04405-876b-45af-9c0a-57c236463d45
-- title:
--   OAI.MetricKMedian.CopyState.enumerated_conditional_round_survival: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset PhysicalPotential FixedBatch`):
--
--   ```lean
--   theorem enumerated_conditional_round_survival (A S : Finset (Copy (F := F) Δ))
--       (G : A → Finset A) (H : Finset A)
--       (enum : Fin n ≃ HeavyAction (graphActions G) H)
--       (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ)
--       {x g h : ℝ} (d : F → ℝ) (hG : ∀ i, (G i).card=Δ)
--       (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (_hh0 : 0 ≤ h)
--       (hprob : (p:ℝ)=2*h*g) (hp : 0 ≤ p ∧ p ≤ 1)
--       (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
--       (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ))
--       (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
--       let D := heavyActions (graphActions G) H
--       let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
--         p q hp hq0).real
--       μ.expect (fun Z => mass g (roundAlive A S G H Z x g d)) ≤ (1-h/2)*mass g S
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect`, `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.FixedBatch.balancedActions` and `OAI.MetricKMedian.FixedBatch.balancedConflicts` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.CopyState.roundAlive` (definitions bundle `OAIQ035K028` of this split); `OAI.MetricKMedian.SparseIntegerLaw.real` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.SparseEnumeratedBatch.law` (definitions bundle `OAIQ035K039` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.RationalBatchData.proposal_survival` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset PhysicalPotential FixedBatch
variable {F : Type} [DecidableEq F] {Δ n : ℕ}

theorem enumerated_conditional_round_survival (A S : Finset (Copy (F := F) Δ))
    (G : A → Finset A) (H : Finset A)
    (enum : Fin n ≃ HeavyAction (graphActions G) H)
    (p : ℚ) (q : HeavyAction (graphActions G) H → ℚ)
    {x g h : ℝ} (d : F → ℝ) (hG : ∀ i, (G i).card=Δ)
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) (_hh0 : 0 ≤ h)
    (hprob : (p:ℝ)=2*h*g) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ 2*(p:ℝ))
    (hsmall : (2*h*g)*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1) (hSA : S ⊆ A) :
    let D := heavyActions (graphActions G) H
    let μ := (SparseEnumeratedBatch.law enum (balancedActions D Δ) (balancedConflicts D Δ)
      p q hp hq0).real
    μ.expect (fun Z => mass g (roundAlive A S G H Z x g d)) ≤ (1-h/2)*mass g S := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
