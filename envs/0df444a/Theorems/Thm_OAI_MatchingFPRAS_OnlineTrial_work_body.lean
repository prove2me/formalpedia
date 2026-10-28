-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineTrial_work_body
-- name    : OAI.MatchingFPRAS.OnlineTrial.work_body
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:11:44.699457+00:00
-- url     : https://prove2.me/theorems/997ab9c9-07d9-4869-877f-d92c874f0f80
-- title:
--   OAI.MatchingFPRAS.OnlineTrial.work_body: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineTrial.work_body` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineStageCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineStageCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineTrial`, with `open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample`):
--
--   ```lean
--   lemma work_body : OnlineTree.WorkBound bodyRealizer (fun x=>stateSize x.2+weight x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableAdaptive.GraphData`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.ExecutableSource.RawLogical`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableSource.StageControls` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableSource.SparseStageData` and `OAI.MatchingFPRAS.TreeTyped.weight` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineTree.WorkBound`, `OAI.MatchingFPRAS.OnlineTrial.State`, `OAI.MatchingFPRAS.OnlineTrial.body`, `OAI.MatchingFPRAS.OnlineTrial.bodyRealizer` and `OAI.MatchingFPRAS.OnlineTrial.stateSize` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.OnlineTrial.sweep_bound` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineStageCost.lean (declaration OAI.MatchingFPRAS.OnlineTrial.work_body)

import Mathlib
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineTrial
open TreeTyped PhysicalStream Polynomial NumericBounds OnlineSchedule OnlineSample

lemma work_body : OnlineTree.WorkBound bodyRealizer (fun x=>stateSize x.2+weight x) := by
  sorry
end MatchingFPRAS.OnlineTrial

end OAI
end
