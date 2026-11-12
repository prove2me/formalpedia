-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialQuery_history_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T12:10:31.518057+00:00
-- url     : https://prove2.me/theorems/2e6d0449-c1ff-4946-b50e-4d325e6c4a87
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/StartResources.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/StartResources.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_computes field_encode)`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`):
--
--   ```lean
--   lemma history_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
--       (F : Finset (Fin m)) (v z lam t : ℚ) (total : ℕ) :
--       history (pairBits (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total,
--         BinaryRational.encode t))=historyBits (initialHistory loc distance F v t total)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryRational.encode` (definitions bundle `Q238L001` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238L008` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.ctx` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteMachine.historyBits` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.initialHistory` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history` (definitions bundle `Q238L043` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.count_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.finishes_pack_s238r`, `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.loopInput_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/StartResources.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitialQuery.history_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialQuery
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_computes field_encode)
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
attribute [local irreducible] BinaryFiniteMachine.continuation

lemma history_pack_s238r {m d : ℕ} (distance : Fin m→Fin d→ℚ) (loc : Fin d→Fin m)
    (F : Finset (Fin m)) (v z lam t : ℚ) (total : ℕ) :
    history (pairBits (ctx (BinaryFiniteContext.pack distance (fun j=>original (loc j)) (F.image original) ∅ v z lam) total,
      BinaryRational.encode t))=historyBits (initialHistory loc distance F v t total) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitialQuery

end OAI
end
