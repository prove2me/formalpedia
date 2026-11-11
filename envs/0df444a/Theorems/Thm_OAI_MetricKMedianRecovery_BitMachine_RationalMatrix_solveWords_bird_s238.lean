-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_solveWords_bird_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:29:23.68367+00:00
-- url     : https://prove2.me/theorems/d2a30cf5-acb1-47e8-ac84-fd06e7890413
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack4.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack4.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix`, with `open WordOperations BinaryArithmetic`, `open WordOperations BinaryArithmetic`, `open scoped Matrix`, `open WordList`):
--
--   ```lean
--   lemma solveWords_bird_s238 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
--       solveWords (pairBits (encode A,rowEncode b))=rowEncode (MetricKMedianRecovery.BirdRational.solve A b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BirdRational.solve` (definitions bundle `Q238K006` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.encode` and `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.rowEncode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords` (definitions bundle `Q238K018` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.point_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Pack4.lean (declaration OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K018

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
open WordOperations BinaryArithmetic
open scoped Matrix
namespace RationalMatrix
open WordList

lemma solveWords_bird_s238 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (b : Fin n → ℚ) :
    solveWords (pairBits (encode A,rowEncode b))=rowEncode (MetricKMedianRecovery.BirdRational.solve A b) := by
  sorry

end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end
