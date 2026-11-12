-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_RationalMatrix_determinantWords_encode_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:38:51.628585+00:00
-- url     : https://prove2.me/theorems/46df854a-fcd3-4300-90a7-93b19e5bf8f0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInput2.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInput2.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix`, with `open WordOperations BinaryArithmetic`, `open WordList`):
--
--   ```lean
--   lemma determinantWords_encode_s238r {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
--       determinantWords (encode A)=BinaryRational.encode A.det
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords` (definitions bundle `Q238L014` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.encode` (definitions bundle `Q238L024` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.solveWords_bird_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInput2.lean (declaration OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.determinantWords_encode)

import Mathlib
import Definitions.Def_Q238L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic
namespace RationalMatrix
open WordList
lemma determinantWords_encode_s238r {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    determinantWords (encode A)=BinaryRational.encode A.det := by
  sorry
end RationalMatrix
end MetricKMedianRecovery.BitMachine

end OAI
end
