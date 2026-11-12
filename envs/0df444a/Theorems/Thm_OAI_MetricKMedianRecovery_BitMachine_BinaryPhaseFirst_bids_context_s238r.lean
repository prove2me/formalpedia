-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_bids_context_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:51:51.228443+00:00
-- url     : https://prove2.me/theorems/ce8b5782-480d-428f-9e45-653246614cda
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability`, `open BinaryOpeningPayment`):
--
--   ```lean
--   lemma bids_context_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
--       (v z lam : ℚ) (i : Fin m) (a : Variables (Fin d) F → ℚ)
--       (ha : storedOpening distance F W v z lam 0 i=some a) :
--       bids (pairBits (context distance F W v z lam,i.val.bits))=
--         RationalMatrix.rowEncode (fun j=>a (.inl j))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalOpenability.Variables` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.RationalMatrix.rowEncode` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids` (definitions bundle `Q238L027` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.context` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.bids_context)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L027
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

lemma bids_context_s238r {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) (a : Variables (Fin d) F → ℚ)
    (ha : storedOpening distance F W v z lam 0 i=some a) :
    bids (pairBits (context distance F W v z lam,i.val.bits))=
      RationalMatrix.rowEncode (fun j=>a (.inl j)) := by
  sorry

end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end
