-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineSchedule_bound_precision
-- name    : OAI.MatchingFPRAS.OnlineSchedule.bound_precision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:09:29.10599+00:00
-- url     : https://prove2.me/theorems/95ef9573-e71b-4a0f-b720-be313d2f590b
-- title:
--   OAI.MatchingFPRAS.OnlineSchedule.bound_precision: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineSchedule.bound_precision` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRequestCost.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRequestCost.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineSchedule`, with `open TreeTyped Polynomial NumericBounds Transport ExecutableSource`):
--
--   ```lean
--   lemma bound_precision : Bound (precisionNorm ∘ sourcePrecision) requestSize
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.NumericBounds.Bound`, `OAI.MatchingFPRAS.OnlineSchedule.PrecisionData` and `OAI.MatchingFPRAS.OnlineSchedule.precisionNorm` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineSchedule.requestSize` and `OAI.MatchingFPRAS.OnlineSchedule.sourcePrecision` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proofs of `OAI.MatchingFPRAS.OnlineGuard.work_checked` and `OAI.MatchingFPRAS.OnlineTrial.work_body` of this split import it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Complexity/OnlineRequestCost.lean (declaration OAI.MatchingFPRAS.OnlineSchedule.bound_precision)

import Mathlib
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Polynomial NumericBounds Transport ExecutableSource

lemma bound_precision : Bound (precisionNorm ∘ sourcePrecision) requestSize := by
  sorry
end MatchingFPRAS.OnlineSchedule

end OAI
end
