-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryExactSolve_transposed_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:38:08.227523+00:00
-- url     : https://prove2.me/theorems/0e6a8d43-885e-4ed1-a4db-e20a03381712
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix`, `open WordList BinaryRationalDecision RationalMatrix`):
--
--   ```lean
--   lemma transposed_pack_s238 {n : ℕ} (rs : List (Row n)) (B : ℕ) :
--       transposed (pack rs B)=Rectangular.encode (rowMatrix (finalFace rs B)).transpose
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.finalFace` and `OAI.MetricKMedianRecovery.Ellipsoid.rowMatrix` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.Rectangular.encode` (definitions bundle `Q238K020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.pack` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed` (definitions bundle `Q238K024` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.gram_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/Rectangular.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack)

import Mathlib
import Definitions.Def_Q238K020
import Definitions.Def_Q238K021
import Definitions.Def_Q238K024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid Matrix
namespace BinaryExactSolve
open WordList BinaryRationalDecision RationalMatrix
lemma transposed_pack_s238 {n : ℕ} (rs : List (Row n)) (B : ℕ) :
    transposed (pack rs B)=Rectangular.encode (rowMatrix (finalFace rs B)).transpose := by
  sorry
end BinaryExactSolve
end MetricKMedianRecovery.BitMachine

end OAI
end
