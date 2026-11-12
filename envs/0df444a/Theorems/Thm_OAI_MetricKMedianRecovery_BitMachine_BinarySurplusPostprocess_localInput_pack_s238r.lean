-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySurplusPostprocess_localInput_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:00:56.139793+00:00
-- url     : https://prove2.me/theorems/37364192-5136-455e-841c-654d3a239eb3
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess`, with `open WordOperations WordList BinaryArithmetic RationalLeaves`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma localInput_pack_s238r (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) :
--       localInput (pack distance F S k)=BinaryLocalRefine.pack distance (F.sort (·≤·))
--         (Completion.Canonical.pad F S (max k S.card))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.Canonical.pad` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLocalRefine.pack` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.pack` (definitions bundle `Q238L031` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput` (definitions bundle `Q238L034` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.integral_spec_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Strictness/SurplusPostprocess.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess.localInput_pack)

import Mathlib
import Definitions.Def_Q238L030
import Definitions.Def_Q238L031
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess
open WordOperations WordList BinaryArithmetic RationalLeaves
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
lemma localInput_pack_s238r (distance : Fin m→Fin d→ℚ) (F S : Finset (Fin m)) (k : ℕ) :
    localInput (pack distance F S k)=BinaryLocalRefine.pack distance (F.sort (·≤·))
      (Completion.Canonical.pad F S (max k S.card)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySurplusPostprocess

end OAI
end
