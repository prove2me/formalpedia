-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_NumericMarking_polynomial_sampleMany
-- name    : OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T18:03:57.370302+00:00
-- url     : https://prove2.me/theorems/95f4f39f-7781-4dd4-99e0-9eefecc79b08
-- title:
--   OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany: intermediate lemma from OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.NumericMarking`, with `open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder`):
--
--   ```lean
--   lemma polynomial_sampleMany : PolynomialTime sampleManyRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.ExecutableDP.Bag`, `OAI.MatchingFPRAS.ExecutableDP.Bags`, `OAI.MatchingFPRAS.ExecutableDP.CountInput`, `OAI.MatchingFPRAS.ExecutableDP.Parents`, `OAI.MatchingFPRAS.ExecutableLadder.StateTable`, `OAI.MatchingFPRAS.ExecutableMarking.Marks`, `OAI.MatchingFPRAS.ExecutableRefresh.Key`, `OAI.MatchingFPRAS.ExecutableUnit.Bits`, `OAI.MatchingFPRAS.NumericLadder.Bits`, `OAI.MatchingFPRAS.NumericLadder.RefreshSetup` and `OAI.MatchingFPRAS.NumericMarking.SampleBits` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableOptions.Options`, `OAI.MatchingFPRAS.NumericLadder.Prepared`, `OAI.MatchingFPRAS.NumericLadder.TierData`, `OAI.MatchingFPRAS.NumericMarking.SampleContext`, `OAI.MatchingFPRAS.NumericMarking.Tables` and `OAI.MatchingFPRAS.TreeTyped.finsetCodec` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.NumericMarking.sampleMany`, `OAI.MatchingFPRAS.NumericMarking.sampleManyRealizer` and `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdate` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Sampling/TreePreparedMarked.lean (declaration OAI.MatchingFPRAS.NumericMarking.polynomial_sampleMany)

import Mathlib
import Definitions.Def_OAIQ051M004

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineMedian.instDecidableRelFractionRelation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatchingFPRAS.NumericMarking
open TreeTyped TreeFraction ExecutableLadder TreeTyped.Numbered UnitRefresh NumericLadder

lemma polynomial_sampleMany : PolynomialTime sampleManyRealizer := by
  sorry

open Replica.Ladder Transport

attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
end MatchingFPRAS.NumericMarking

end OAI
end
