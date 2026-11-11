-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryPhaseFirst_eligible_context_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:43:44.692858+00:00
-- url     : https://prove2.me/theorems/f81584c1-6b52-421c-bdbd-8647a20e6784
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst`, with `open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability`, `open BinaryOpeningPayment`):
--
--   ```lean
--   lemma eligible_context_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
--       (v z lam : ℚ) (i : Fin m) : eligible (pairBits (context distance F W v z lam,i.val.bits))=
--         decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalOpenability.Variables` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.EffectiveOpenability.storedOpening` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible` (definitions bundle `Q238K024` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.context` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.answer_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFinish.finish_length_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseRun.finish_bound_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseTrace.iterate_length_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/RowInput.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryPhaseFirst.eligible_context)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K022
import Definitions.Def_Q238K024
import Definitions.Def_Q238K026

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseFirst
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalOpenability
open BinaryOpeningPayment

lemma eligible_context_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F W : Finset (Fin m))
    (v z lam : ℚ) (i : Fin m) : eligible (pairBits (context distance F W v z lam,i.val.bits))=
      decide (i∈F ∧ i∉W ∧ storedOpening distance F W v z lam 0 i≠none) := by
  sorry

end MetricKMedianRecovery.BitMachine.BinaryPhaseFirst

end OAI
end
