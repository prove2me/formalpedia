-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_selected_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:39:09.04652+00:00
-- url     : https://prove2.me/theorems/f2d5ee5b-9492-4d56-b75e-df82da4e9721
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext`, with `open Classical`, `open WordOperations WordList BinaryOpeningPayment RationalLeaves`, `open BinaryLabel (orderedSort)`):
--
--   ```lean
--   lemma selected_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F Q S : Finset (Label (Fin m))) (v z lam : ℚ) (k : ℕ)
--       (hk : field k (pack distance loc F Q v z lam)=setBits S) :
--       selected k (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
--         ((EffectiveOpenability.subtypeList (FiniteLabelContinuation.select loc F Q S)).map Subtype.val)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningPayment.field` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.subtypeList` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.alphabet` and `OAI.MetricKMedianRecovery.FiniteLabelContinuation.select` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryOpeningActivity.indices` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder` and `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected` (definitions bundle `Q238K025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238K026` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.advanceInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.c_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.crossInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.finishInput_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.completed_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.chosen_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryScan.nodes_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteContext.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.selected_pack)

import Mathlib
import Definitions.Def_Q238K025
import Definitions.Def_Q238K026

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open Classical
open WordOperations WordList BinaryOpeningPayment RationalLeaves
open BinaryLabel (orderedSort)

lemma selected_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q S : Finset (Label (Fin m))) (v z lam : ℚ) (k : ℕ)
    (hk : field k (pack distance loc F Q v z lam)=setBits S) :
    selected k (pack distance loc F Q v z lam)=BinaryOpeningActivity.indices
      ((EffectiveOpenability.subtypeList (FiniteLabelContinuation.select loc F Q S)).map Subtype.val) := by
  sorry

attribute [local irreducible] BinaryLabelMatrix.run
attribute [local irreducible] matrix selected
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end
