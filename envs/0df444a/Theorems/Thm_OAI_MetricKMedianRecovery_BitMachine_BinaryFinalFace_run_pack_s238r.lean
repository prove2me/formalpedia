-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFinalFace_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:48:38.789532+00:00
-- url     : https://prove2.me/theorems/e1980248-7485-4a70-8f7f-e9a261f54cd9
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FaceSelection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FaceSelection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid`, `open WordList BinaryRationalDecision`):
--
--   ```lean
--   lemma run_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=BinaryRow.rowsEncode (finalFace rs B)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.finalFace` (definitions bundle `Q238L009` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run` (definitions bundle `Q238L022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRow.rowsEncode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRationalDecision.pack` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.rhs_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryExactSolve.transposed_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FaceSelection.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFinalFace.run_pack)

import Mathlib
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine
open WordOperations BinaryArithmetic RationalLinearFeasibility Ellipsoid
namespace BinaryFinalFace
open WordList BinaryRationalDecision
lemma run_pack_s238r {n : ℕ} (rs : List (Row n)) (B : ℕ) : run (pack rs B)=BinaryRow.rowsEncode (finalFace rs B) := by
  sorry
end BinaryFinalFace
end MetricKMedianRecovery.BitMachine

end OAI
end
