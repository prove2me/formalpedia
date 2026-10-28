-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineInitial_work_initializeInput
-- name    : OAI.MatchingFPRAS.OnlineInitial.work_initializeInput
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:14:30.788102+00:00
-- url     : https://prove2.me/theorems/bc9e851d-e171-4d54-8695-a03fa30e78b5
-- title:
--   OAI.MatchingFPRAS.OnlineInitial.work_initializeInput: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineInitial.work_initializeInput` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineInitialDataCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineInitialDataCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineInitial`, with `open TreeTyped TreeFraction OnlineSchedule Polynomial NumericBounds ExecutableSource ExecutableScaling`):
--
--   ```lean
--   lemma work_initializeInput : WorkBound initializeInputRealizer seedSize
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableAdaptive.GraphData`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.ExecutableSource.RawLogical`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableSource.StageControls` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableSource.SparseStageData` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.OnlineInitial.Seed` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.OnlineAmplification.TrialInput`, `OAI.MatchingFPRAS.OnlineInitial.initializeInput`, `OAI.MatchingFPRAS.OnlineInitial.initializeInputRealizer`, `OAI.MatchingFPRAS.OnlineInitial.seedSize`, `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineTrial.State` and `OAI.MatchingFPRAS.TreeTyped.WorkBound` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.LiteralAlgorithm.algorithm_bound` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineInitialDataCost.lean (declaration OAI.MatchingFPRAS.OnlineInitial.work_initializeInput)

import Mathlib
import Definitions.Def_OAIQ051M004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineInitial
open TreeTyped TreeFraction OnlineSchedule Polynomial NumericBounds ExecutableSource ExecutableScaling

lemma work_initializeInput : WorkBound initializeInputRealizer seedSize := by
  sorry
end MatchingFPRAS.OnlineInitial

end OAI
end
