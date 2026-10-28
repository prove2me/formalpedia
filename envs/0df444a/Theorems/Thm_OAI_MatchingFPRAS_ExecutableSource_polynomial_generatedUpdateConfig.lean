-- Prove2me | Theorems.Thm_OAI_MatchingFPRAS_ExecutableSource_polynomial_generatedUpdateConfig
-- name    : OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T17:51:20.841914+00:00
-- url     : https://prove2.me/theorems/ac1a8d67-e0c5-4a06-a75d-0837f6fe6499
-- title:
--   OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MatchingFPRAS.thm_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113)*, OpenAI Math Release, September 23, 2026, result family 113, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig` of [lean/OAI/Combinatorics/MatchingCount/MatchingCount/Machines/TreeBindings.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Machines/TreeBindings.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MatchingFPRAS.ExecutableSource`, with `open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking`):
--
--   ```lean
--   lemma polynomial_generatedUpdateConfig : PolynomialTime generatedUpdateConfigRealizer
--   ```
--
--   **Definitions.** The statement is written with `OAI.MatchingFPRAS.ExecutableScaling.Vector`, `OAI.MatchingFPRAS.TreeFraction.Fraction`, `OAI.MatchingFPRAS.TreeTyped.instCodecBool`, `OAI.MatchingFPRAS.TreeTyped.instCodecList`, `OAI.MatchingFPRAS.TreeTyped.instCodecNat` and `OAI.MatchingFPRAS.TreeTyped.instCodecProd` (definitions bundle `OAIQ051M000` of this split); `OAI.MatchingFPRAS.NumericMarking.Bindings` (definitions bundle `OAIQ051M001` of this split); `OAI.MatchingFPRAS.ExecutableBottleneck.Matrix`, `OAI.MatchingFPRAS.ExecutableSource.BagBuildInput`, `OAI.MatchingFPRAS.ExecutableSource.BuildInput` and `OAI.MatchingFPRAS.ExecutableSource.GeneratedUpdateConfig` (definitions bundle `OAIQ051M002` of this split); `OAI.MatchingFPRAS.NumericMarking.UpdateConfig` (definitions bundle `OAIQ051M003` of this split); `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateConfig`, `OAI.MatchingFPRAS.ExecutableSource.generatedUpdateConfigRealizer` and `OAI.MatchingFPRAS.TreeTyped.PolynomialTime` (definitions bundle `OAIQ051M004` of this split).
--
--   **Used by.** The proof of `OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdate` of this split imports it.
-- source:
--   OpenAI, A Fully Polynomial Randomized Approximation Scheme for Perfect Matchings in General Graphs (result family 113), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 113; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Fully-Polynomial-Randomized-Approximation-Scheme-for-Perfect-Matchings-in-General-Graphs-September-23-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/MatchingCount/MatchingCount/Machines/TreeBindings.lean (declaration OAI.MatchingFPRAS.ExecutableSource.polynomial_generatedUpdateConfig)

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
open TreeTyped TreeFraction TreeTyped.Numbered ExecutableBottleneck ExecutableHierarchy ExecutableRefresh Enlargement RealGeometry NumericLadder ExecutableLadder NumericMarking

attribute [local instance] NumberedHierarchy.labelOrder
attribute [local instance] Transport.sym2Order Transport.bagEdgeOrder Transport.bagEdgeFintype
attribute [local instance] UnitRefresh.Computable.allowedDec Transport.prodOrder Transport.sumOrder
lemma polynomial_generatedUpdateConfig : PolynomialTime generatedUpdateConfigRealizer := by
  sorry

end MatchingFPRAS.ExecutableSource

end OAI
end
