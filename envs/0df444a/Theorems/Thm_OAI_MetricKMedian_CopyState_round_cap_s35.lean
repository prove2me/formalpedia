-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_round_cap_s35
-- name    : OAI.MetricKMedian.CopyState.round_cap_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:35:40.473506+00:00
-- url     : https://prove2.me/theorems/fe985162-b447-455a-9933-dc9c3530de75
-- title:
--   OAI.MetricKMedian.CopyState.round_cap_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset PhysicalPotential FixedBatch`):
--
--   ```lean
--   theorem round_cap_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
--       (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (R : ℝ) (d : F → ℝ)
--       (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
--       GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)))=
--         nextCap (heavyActions (graphActions G) H) (fun i => d i.val.1)
--           (GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)) Z
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy`, `OAI.MetricKMedian.CopyState.integral` and `OAI.MetricKMedian.CopyState.own` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions` and `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.GroupCap.cap` (definitions bundle `OAIQ035K008` of this split); `OAI.MetricKMedian.CopyState.forcedGroups`, `OAI.MetricKMedian.CopyState.next` and `OAI.MetricKMedian.CopyState.roundErased` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.CopyState.roundOpened` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.nextCap` (definitions bundle `OAIQ035K021` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.CopyState.rational_conditional_round_drift_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
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
open Finset PhysicalPotential FixedBatch
variable {F : Type*} [DecidableEq F] [Fintype F] {Δ : ℕ}

theorem round_cap_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (Z : Finset (HeavyAction (graphActions G) H)) (R : ℝ) (d : F → ℝ)
    (hG : ∀ i, (G i).card=Δ) (hown : ∀ i, own Δ A i ⊆ G i) :
    GroupCap.cap R d (integral Δ (next Δ A (roundErased A G H Z) (roundOpened A G H Z)))=
      nextCap (heavyActions (graphActions G) H) (fun i => d i.val.1)
        (GroupCap.cap R d (integral Δ A ∪ forcedGroups A H)) Z := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
