-- Prove2me | Theorems.Thm_OAI_MetricKMedian_FixedBatch_forced_step_local_bound_s53
-- name    : OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:34:23.086513+00:00
-- url     : https://prove2.me/theorems/c7d25309-504f-468c-869a-f9bb6c3bad7a
-- title:
--   OAI.MetricKMedian.FixedBatch.forced_step_local_bound_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.FixedBatch.forced_step_local_bound` of [lean/OAI/Combinatorics/KMedian/Process/ForcedLocal.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/ForcedLocal.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.FixedBatch`, with `open Finset PhysicalPotential Analytic`):
--
--   ```lean
--   theorem forced_step_local_bound_s53 (D : Actions I E) (Full : Actions I H)
--       (μ : FiniteLaw (Finset E)) {x g h b b' : ℝ} {N : ℕ}
--       (d : I → ℝ) (S F : Finset I)
--       (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
--       (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
--       (hsmall : (16*(N:ℝ)+10)*h ≤ savingsFraction g)
--       (hy : mass g S ≤ 1) (hF : F ⊆ S) (hδ : g ≤ mass g F)
--       (hd0 : ∀ i, 0 ≤ d i) (hb0 : 0 ≤ b)
--       (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
--       (hb'0 : 0 ≤ b') (hb' : b' ≤ b) (hbF : ∀ i ∈ F, b' ≤ d i)
--       (hD : (relevant D S).card ≤ N) (hFull : (relevant Full S).card ≤ N)
--       (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
--       μ.expect (fun A => potential (x*Real.exp (-h)) g d
--         (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
--         (nextCap D d b' A)-potential x g d S b) ≤
--         h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
--           g*(∑ e ∈ relevant Full S, charge Full x g b d S e))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Analytic.coefficient` and `OAI.MetricKMedian.Analytic.timeRate` (definitions bundle `OAIQ053K000` of this split); `OAI.MetricKMedian.FiniteLaw`, `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FixedBatch.Actions` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.PhysicalPotential.cost` (definitions bundle `OAIQ053K007` of this split); `OAI.MetricKMedian.PhysicalPotential.savingsFraction` (definitions bundle `OAIQ053K015` of this split); `OAI.MetricKMedian.FiniteLaw.prob`, `OAI.MetricKMedian.FixedBatch.nextAliveAt` and `OAI.MetricKMedian.FixedBatch.relevant` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.FixedBatch.charge`, `OAI.MetricKMedian.FixedBatch.nextCap` and `OAI.MetricKMedian.PhysicalPotential.potential` (definitions bundle `OAIQ053K020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseEnumeratedFixedBatch.actual_local_bound_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/ForcedLocal.lean (declaration OAI.MetricKMedian.FixedBatch.forced_step_local_bound)

import Mathlib
import Definitions.Def_OAIQ053K015
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020

section

attribute [-instance] _root_.OAI.MetricKMedian.Complexity.FiniteComposition.Thread.alphabetFinite _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E H : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]
  [DecidableEq H] [Fintype H]

theorem forced_step_local_bound_s53 (D : Actions I E) (Full : Actions I H)
    (μ : FiniteLaw (Finset E)) {x g h b b' : ℝ} {N : ℕ}
    (d : I → ℝ) (S F : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg0 : 0 < g) (hg1 : g ≤ 1)
    (hh0 : 0 ≤ h) (hh1 : h ≤ 1)
    (hsmall : (16*(N:ℝ)+10)*h ≤ savingsFraction g)
    (hy : mass g S ≤ 1) (hF : F ⊆ S) (hδ : g ≤ mass g F)
    (hd0 : ∀ i, 0 ≤ d i) (hb0 : 0 ≤ b)
    (hbQ : b ≤ 5*((PhysicalPotential.cost g d S+(1-mass g S)*b)/g))
    (hb'0 : 0 ≤ b') (hb' : b' ≤ b) (hbF : ∀ i ∈ F, b' ≤ d i)
    (hD : (relevant D S).card ≤ N) (hFull : (relevant Full S).card ≤ N)
    (hmarg : ∀ e ∈ relevant D S, μ.prob (fun A => e ∈ A) ≤ 2*h*g) :
    μ.expect (fun A => potential (x*Real.exp (-h)) g d
      (nextAliveAt D (coefficient x (mass g S)) d (S \ F) A)
      (nextCap D d b' A)-potential x g d S b) ≤
      h*(timeRate x (mass g S)*PhysicalPotential.cost g d S+
        g*(∑ e ∈ relevant Full S, charge Full x g b d S e)) := by
  sorry

end MetricKMedian.FixedBatch
end
end

end OAI
end
