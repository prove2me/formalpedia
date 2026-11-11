-- Prove2me | Theorems.Thm_OAI_MetricKMedian_CopyState_balanced_count_change_s35
-- name    : OAI.MetricKMedian.CopyState.balanced_count_change_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T15:13:33.948677+00:00
-- url     : https://prove2.me/theorems/166b35e5-6448-46a3-a1e6-828fea21af11
-- title:
--   OAI.MetricKMedian.CopyState.balanced_count_change_s35: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedian.CopyState.balanced_count_change` of [lean/OAI/Combinatorics/KMedian/Process/PhysicalCountGeometry.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalCountGeometry.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.CopyState`, with `open Finset FixedBatch PhysicalPotential`):
--
--   ```lean
--    theorem balanced_count_change_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
--       (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
--       (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
--       let D := heavyActions (graphActions G) H
--       let Z := PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω
--       mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ H.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.CopyState.Copy` and `OAI.MetricKMedian.PhysicalPotential.mass` (definitions bundle `OAIQ035K003` of this split); `OAI.MetricKMedian.FixedBatch.Actions`, `OAI.MetricKMedian.FixedBatch.HeavyAction`, `OAI.MetricKMedian.FixedBatch.graphActions`, `OAI.MetricKMedian.FixedBatch.heavyActions`, `OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction` and `OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.CopyState.next` and `OAI.MetricKMedian.CopyState.roundErased` (definitions bundle `OAIQ035K015` of this split); `OAI.MetricKMedian.CopyState.roundOpened` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.balancedActions` and `OAI.MetricKMedian.FixedBatch.balancedConflicts` (definitions bundle `OAIQ035K021` of this split); `OAI.MetricKMedian.PhysicalBatchLaw.balanced` (definitions bundle `OAIQ035K024` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.SparseCopyState.physical_count_tail_s35` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedian/Process/PhysicalCountGeometry.lean (declaration OAI.MetricKMedian.CopyState.balanced_count_change)

import Mathlib
import Definitions.Def_OAIQ035K015
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.CopyState
open Finset FixedBatch PhysicalPotential
variable {F : Type*} [DecidableEq F] {Δ : ℕ}

 theorem balanced_count_change_s35 (A : Finset (Copy (F := F) Δ)) (G : A → Finset A)
    (H : Finset A) (ω : HeavyAction (graphActions G) H → Bool) {g : ℝ}
    (hg : 0 ≤ g) (hunit : g*(Δ:ℝ)=1) :
    let D := heavyActions (graphActions G) H
    let Z := PhysicalBatchLaw.balanced (balancedActions D Δ) (balancedConflicts D Δ) ω
    mass g (next Δ A (roundErased A G H Z) (roundOpened A G H Z))-mass g A ≤ H.card := by
  sorry

end MetricKMedian.CopyState
end
end

end OAI
end
