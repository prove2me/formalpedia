-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueBlocks_at_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:36:52.093633+00:00
-- url     : https://prove2.me/theorems/5fa413bb-da2c-4404-a998-40ceef240ad3
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueBlocksMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueBlocksMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks`, with `open WordOperations WordList`):
--
--   ```lean
--   lemma at_pack_s238r (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R)
--       (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) (y : Fin n) :
--       atCenter (pairBits (pairBits (BinaryBlueItem.records el er B label q,y.val.bits),labelsEnc el U))=
--         BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) (BlueDP.blockAt B label q U y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BlueDP.Atom` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BlueDP.blockAt` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.labelsEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueItem.records` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.listEnc` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.atCenter` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.op_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueBlocksMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBlueBlocks.at_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueBlocks
open WordOperations WordList
variable {L R : Type*} [LinearOrder L] [LinearOrder R] {n : ℕ}
lemma at_pack_s238r (el : L→List Bool) (er : R→List Bool) (hel : Function.Injective el) (B : Finset R)
    (label : R→L) (q : R→Fin n→ℚ) (U : Finset L) (y : Fin n) :
    atCenter (pairBits (pairBits (BinaryBlueItem.records el er B label q,y.val.bits),labelsEnc el U))=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueItem.atomEnc el er)) (BlueDP.blockAt B label q U y) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBlueBlocks

end OAI
end
