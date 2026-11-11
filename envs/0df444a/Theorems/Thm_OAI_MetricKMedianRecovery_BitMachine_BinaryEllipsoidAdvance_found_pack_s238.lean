-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryEllipsoidAdvance_found_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:26:28.379944+00:00
-- url     : https://prove2.me/theorems/736d6f58-a614-46af-9db4-3ecd6cd863df
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Encoding/OptionEncode.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/OptionEncode.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance`, with `open WordOperations BinaryArithmetic RationalLinearFeasibility`, `open Ellipsoid RationalMatrix`, `open scoped Matrix`):
--
--   ```lean
--   lemma found_pack_s238 {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
--       found (pack D rs S)=WordList.Find.optionEncode ((badRow rs S.center).map BinaryRow.encode)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLinearFeasibility.Row` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.State` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Find.optionEncode` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found` (definitions bundle `Q238K007` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryRow.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.Ellipsoid.badRow` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.pack` (definitions bundle `Q238K021` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBoundedDecision.run_pack_s238`, `OAI_MetricKMedianRecovery_BitMachine_BinaryDecision_run_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidIteration.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Encoding/OptionEncode.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryEllipsoidAdvance.found_pack)

import Mathlib
import Definitions.Def_Q238K021

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine

open WordOperations BinaryArithmetic RationalLinearFeasibility
namespace BinaryEllipsoidAdvance
open Ellipsoid RationalMatrix
open scoped Matrix

lemma found_pack_s238 {n : ℕ} (D : ℕ) (rs : List (Row n)) (S : State n) :
    found (pack D rs S)=WordList.Find.optionEncode ((badRow rs S.center).map BinaryRow.encode) := by
  sorry
end BinaryEllipsoidAdvance
end MetricKMedianRecovery.BitMachine

end OAI
end
