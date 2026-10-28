-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_unbalanced_small_change_s35
-- name    : OAI.MetricKMedian.CopyState.unbalanced_small_change_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:35:41.406583+00:00
-- url     : https://prove2.me/theorems/f93a6da4-c37e-417b-be6b-ac3ee6d14c63
-- title:
--   OAI.MetricKMedian.CopyState.unbalanced_small_change_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset FixedBatch PhysicalPotential SourceBalance CountStatistic`):
--
--   ```lean
--   theorem unbalanced_small_change_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
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
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.unbalanced` and `OAI.MetricKMedian.SourceBalance.amount` (definitions bundle `OAIQ035K011` of this split); `OAI.MetricKMedian.CopyState.next` and `OAI.MetricKMedian.CopyState.roundErased` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.CopyState.roundOpened` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.balancedActions` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K011
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021

section

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

theorem unbalanced_small_change_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
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
