-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_OnlineSchedule_polynomial_sourceRequest
-- name    : OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:11:19.695355+00:00
-- url     : https://prove2.me/theorems/f5641352-f36a-4d10-86be-7a438e864101
-- title:
--   OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineRequest.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineRequest.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.OnlineSchedule`, with `open TreeTyped TreeFraction Transport ExecutableSource NumericLadder ExecutableScaling`, `open TreeTyped.Numbered Enlargement UnitRefresh ExecutableAdaptive`, `open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh`):
--
--   ```lean
--   lemma polynomial_sourceRequest : PolynomialTime sourceRequestRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableAdaptive.GraphData`, `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.ExecutableSource.RawLogical`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableSource.StageControls` and `OAI.MatchingFPRAS.OnlineSample.Request` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableSource.SparseStageData` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.OnlineSchedule.RequestInput`, `OAI.MatchingFPRAS.OnlineSchedule.sourceRequest`, `OAI.MatchingFPRAS.OnlineSchedule.sourceRequestRealizer` and `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proofs of `OAI.MatchingFPRAS.OnlineGuard.work_checked` and `OAI.MatchingFPRAS.OnlineTrial.work_body` of this split import it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/OnlineRequest.lean (declaration OAI.MatchingFPRAS.OnlineSchedule.polynomial_sourceRequest)

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
open TreeTyped TreeFraction Transport ExecutableSource NumericLadder ExecutableScaling
open TreeTyped.Numbered Enlargement UnitRefresh ExecutableAdaptive
open ExecutableBottleneck ExecutableHierarchy ExecutableRefresh

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma polynomial_sourceRequest : PolynomialTime sourceRequestRealizer := by
  sorry

end MatchingFPRAS.OnlineSchedule

end OAI
end
