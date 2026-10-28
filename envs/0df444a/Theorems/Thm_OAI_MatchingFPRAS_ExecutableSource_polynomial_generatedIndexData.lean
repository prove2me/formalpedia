-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_ExecutableSource_polynomial_generatedIndexData
-- name    : OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:01:10.842486+00:00
-- url     : https://prove2.me/theorems/bb031ca7-210b-47b4-9be1-9ab71b8765eb
-- title:
--   OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/TreeGeneratedStage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/TreeGeneratedStage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.ExecutableSource`, with `open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder`, `open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics`):
--
--   ```lean
--   lemma polynomial_generatedIndexData : PolynomialTime generatedIndexDataRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableBottleneck.Matrix`, `OAI.MatchingFPRAS.ExecutableSource.BagBuildInput`, `OAI.MatchingFPRAS.ExecutableSource.BuildInput`, `OAI.MatchingFPRAS.ExecutableSource.GeneratedInput` and `OAI.MatchingFPRAS.ExecutableSource.GeneratedStageData` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.ExecutableSource.generatedIndexData`, `OAI.MatchingFPRAS.ExecutableSource.generatedIndexDataRealizer` and `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdate` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Algorithm/TreeGeneratedStage.lean (declaration OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedIndexData)

import Mathlib
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.ExecutableSource
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder
open ExecutableLadder UnitRefresh Replica.Ladder Transport NumericMarking ExecutableStatistics

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder

lemma polynomial_generatedIndexData : PolynomialTime generatedIndexDataRealizer := by
  sorry

open TreePost Turing

end MatchingFPRAS.ExecutableSource

end OAI
end
