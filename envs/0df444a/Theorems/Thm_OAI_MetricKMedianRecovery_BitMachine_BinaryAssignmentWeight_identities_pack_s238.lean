-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryAssignmentWeight_identities_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:34:03.868339+00:00
-- url     : https://prove2.me/theorems/e01addec-0909-4775-9e2a-6889ca1089b7
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchWeights.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchWeights.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma identities_pack_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
--       identities (BinarySamplingOracle.pack δ D S Δ s)=encode ((D.sort (·≤·)).map (fun p=>(RationalSampling.chosenId δ S Δ s p).bits))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.RationalSampling.State` and `OAI.MetricKMedianRecovery.RationalSampling.chosenId` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySamplingOracle.pack` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities` (definitions bundle `Q238K025` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.bluePack_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.completion_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.completion_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BranchWeights.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight.identities_pack)

import Mathlib
import Definitions.Def_Q238K025

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n : ℕ}
lemma identities_pack_s238 (δ : Fin n→Fin n→ℚ) (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    identities (BinarySamplingOracle.pack δ D S Δ s)=encode ((D.sort (·≤·)).map (fun p=>(RationalSampling.chosenId δ S Δ s p).bits)) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryAssignmentWeight

end OAI
end
