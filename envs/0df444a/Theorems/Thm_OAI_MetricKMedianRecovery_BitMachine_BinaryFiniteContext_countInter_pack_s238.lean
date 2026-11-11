-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryFiniteContext_countInter_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:49:02.308481+00:00
-- url     : https://prove2.me/theorems/f7ba8fce-eabe-4cfc-8f09-6a612327e624
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext`, with `open WordOperations WordList RationalLeaves BinaryArithmetic`):
--
--   ```lean
--   lemma countInter_pack_s238 {m : ℕ} (S T : Finset (Label (Fin m))) :
--       countInter (pairBits (setBits S,setBits T))=(S∩T).card.bits
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.setBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter` (definitions bundle `Q238K029` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledStep.a_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.edge_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCross.finalCount_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryLengthQuery.count_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.countInter_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K029

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryFiniteContext
open WordOperations WordList RationalLeaves BinaryArithmetic
lemma countInter_pack_s238 {m : ℕ} (S T : Finset (Label (Fin m))) :
    countInter (pairBits (setBits S,setBits T))=(S∩T).card.bits := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryFiniteContext

end OAI
end
