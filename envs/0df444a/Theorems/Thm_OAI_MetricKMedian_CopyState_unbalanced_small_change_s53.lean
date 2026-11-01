-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_unbalanced_small_change_s53
-- name    : OAI.MetricKMedian.CopyState.unbalanced_small_change_s53
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T06:33:41.356242+00:00
-- url     : https://prove2.me/theorems/ba6fb94a-d8b2-45a1-9e51-763a264a1a6f
-- title:
--   OAI.MetricKMedian.CopyState.unbalanced_small_change_s53: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.CopyState.unbalanced_small_change` of [lean/OAI/Combinatorics/KMedian/Process/PhysicalCountLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalCountLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic`):
--
--   ```lean
--   theorem unbalanced_small_change_s53 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
--       {g b : ℝ} (hg : 0 < g) (hb : 0 < b) (hunit : g*(Δ:ℝ)=1)
--       (hG : ∀ i, (G i).card=Δ)
--       (hsmall : b*amount (fun h => mass g ((graphActions G).erase h)) ≤ 1) :
--       let m := fun h => mass g ((graphActions G).erase h)
--       let H := univ.filter (fun h => max 1 (b*amount m) < m h)
--       ∀ ω : HeavyAction (graphActions G) H → Bool,
--         let D := heavyActions (graphActions G) H
--         let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
--         mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ 4/(g*b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` (definitions bundle `OAIQ053K002` of this split); `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ053K004` of this split); `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ053K005` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.unbalanced` (definitions bundle `OAIQ053K011` of this split); `OAI.MetricKMedian.SourceBalance.amount` (definitions bundle `OAIQ053K012` of this split); `OAI.MetricKMedian.CopyState.next` (definitions bundle `OAIQ053K017` of this split); `OAI.MetricKMedian.CopyState.roundErased`, `OAI.MetricKMedian.CopyState.roundOpened`, `OAI.MetricKMedian.FixedBatch.graphActions` and `OAI.MetricKMedian.FixedBatch.heavyActions` (definitions bundle `OAIQ053K018` of this split); `OAI.MetricKMedian.FixedBatch.balancedActions` (definitions bundle `OAIQ053K020` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s53` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalCountLaw.lean (declaration OAI.MetricKMedian.CopyState.unbalanced_small_change)

import Mathlib
import Definitions.Def_OAIQ053K011
import Definitions.Def_OAIQ053K012
import Definitions.Def_OAIQ053K017
import Definitions.Def_OAIQ053K018
import Definitions.Def_OAIQ053K020

section

attribute [-instance] _root_.OAI.MetricKMedian.PCP.LocalRelation.instDecidableEqVars
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

theorem unbalanced_small_change_s53 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    {g b : ℝ} (hg : 0 < g) (hb : 0 < b) (hunit : g*(Δ:ℝ)=1)
    (hG : ∀ i, (G i).card=Δ)
    (hsmall : b*amount (fun h => mass g ((graphActions G).erase h)) ≤ 1) :
    let m := fun h => mass g ((graphActions G).erase h)
    let H := univ.filter (fun h => max 1 (b*amount m) < m h)
    ∀ ω : HeavyAction (graphActions G) H → Bool,
      let D := heavyActions (graphActions G) H
      let Z := PhysicalBatchLaw.unbalanced (balancedActions D Δ) ω
      mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ 4/(g*b) := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
