-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySamplingOracle_reference_pair_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:44:50.903212+00:00
-- url     : https://prove2.me/theorems/a0c449c5-f99b-4bb5-85df-2d5617e937a0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma reference_pair_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
--       reference (pairBits (pack δ D S Δ s,w.val.bits))=
--         pairBits (BinaryRational.encode (RationalSampling.reference δ S Δ s w),(RationalSampling.chosenId δ S Δ s w).bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State`, `OAI.MetricKMedianRecovery.RationalSampling.chosenId` and `OAI.MetricKMedianRecovery.RationalSampling.reference` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.pack` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference` (definitions bundle `Q238K025` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_one_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRows.capRow_zero_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.remove_pair_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinarySampler.Update.run_pair_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.weight_pair_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SamplingStateMachine.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.reference_pair)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySamplingOracle
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
lemma reference_pair_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) (w : Fin n) :
    reference (pairBits (pack δ D S Δ s,w.val.bits))=
      pairBits (BinaryRational.encode (RationalSampling.reference δ S Δ s w),(RationalSampling.chosenId δ S Δ s w).bits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySamplingOracle

end OAI
end
