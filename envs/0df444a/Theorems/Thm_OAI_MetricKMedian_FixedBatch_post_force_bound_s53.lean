-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_post_force_bound_s53
-- name    : OAI.MetricKMedian.FixedBatch.post_force_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:35:12.252995+00:00
-- url     : https://prove2.me/theorems/a555f00e-7705-4f1e-a9a4-6865954ff43f
-- title:
--   OAI.MetricKMedian.FixedBatch.post_force_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FixedBatch.post_force_bound` of [lean/OAI/Combinatorics/KMedian/Process/ForceBatchBound.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/ForceBatchBound.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential Analytic`):
--
--   ```lean
--   theorem post_force_bound_s53 (D : Actions I E) (μ : FiniteLaw (Finset E))
--       {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
--       (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
--       (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
--       (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
--       (hcap : ∀ A, 0 ≤ nextCap D d b A)
--       (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
--       μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
--         (nextCap D d b A)-potential x g d S b) ≤
--         (8*((relevant D S).card:ℝ)+8)*h*V
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FixedBatch.Actions` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FixedBatch.nextAliveAt` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.FixedBatch.nextCap` and `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/ForceBatchBound.lean (declaration OAI.MetricKMedian.FixedBatch.post_force_bound)

import Mathlib
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020

section

attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

theorem post_force_bound_s53 (D : Actions I E) (μ : FiniteLaw (Finset E))
    {x g h b V : ℝ} (a : ℝ) (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1) (hV : 0 ≤ V)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1)
    (hVS : PhysicalPotential.cost g d S ≤ V) (hb0 : 0 ≤ b) (hbV : b ≤ V/g)
    (hcap : ∀ A, 0 ≤ nextCap D d b A)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d (nextAliveAt D a d S A)
      (nextCap D d b A)-potential x g d S b) ≤
      (8*((relevant D S).card:ℝ)+8)*h*V := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end
