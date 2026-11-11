-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCompletion_saving_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:10.747264+00:00
-- url     : https://prove2.me/theorems/e2fef4a7-33cf-40b1-8dfe-67d4aaece712
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes )`):
--
--   ```lean
--   lemma saving_pack_s238 (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
--       (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
--       saving (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
--         BinaryRational.encode (savingQ k base distance weight redBase redDistance xs.toFinset)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` and `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.savingQ` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elemBits` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.contextBits` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving` (definitions bundle `Q238K037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/RationalSurrogate.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCompletion.saving_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCompletion
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
variable {q p r : ℕ}
lemma saving_pack_s238 (k : ℕ) (base : Fin p→ℚ) (distance : Fin p→Fin q→ℚ)
    (weight redBase : Fin r→ℚ) (redDistance : Fin r→Fin q→ℚ) (xs : List (Fin q)) :
    saving (pairBits (contextBits k base distance weight redBase redDistance,encode (xs.map BinaryCategorical.elemBits)))=
      BinaryRational.encode (savingQ k base distance weight redBase redDistance xs.toFinset) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCompletion

end OAI
end
