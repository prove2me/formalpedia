-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryMatch_step_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:12:18.770618+00:00
-- url     : https://prove2.me/theorems/cfaf1515-e4be-437e-b506-8ceb8d8f4cef
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchFold.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchFold.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch`, with `open WordOperations WordList RationalLeaves CanonicalMatch`, `open BinaryFiniteContext (labels setBits)`, `open BinaryFiniteMachine (historyBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma step_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
--       (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
--       (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
--       step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
--         pairBits (BinaryLabel.encode a,accBits s)))=
--         accBits (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMatch.Acc` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryLabel.encode` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.CanonicalMatch.step` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder`, `OAI.MetricKMedianRecovery.RationalLeaves.rows` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.accBits` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.FiniteLabelContinuation.complete` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy`, `OAI.MetricKMedianRecovery.BitMachine.BinaryFiniteContext.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.contextBits` (definitions bundle `Q238K026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step` (definitions bundle `Q238K043` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.run_pack_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/MatchFold.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryMatch.step_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K043

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryMatch
open WordOperations WordList RationalLeaves CanonicalMatch
open BinaryFiniteContext (labels setBits)
open BinaryFiniteMachine (historyBits)
open BinaryOpeningPayment (field field_computes field_encode)

attribute [local irreducible] BinaryLabel.copied
attribute [local irreducible] advanced
lemma step_pack_s238 {m d : ℕ} (distance : Fin m → Fin d → ℚ) (loc : Fin d → Label (Fin m))
    (F Q : Finset (Label (Fin m))) (v z lam : ℚ) (key : ℕ)
    (s : Acc (Label (Fin m))) (a : Label (Fin m)) :
    step (pairBits (contextBits (BinaryFiniteContext.pack distance loc F Q v z lam) key F,
      pairBits (BinaryLabel.encode a,accBits s)))=
      accBits (CanonicalMatch.step (FiniteLabelContinuation.complete loc (rows distance) F v z lam) Q (copy key) s a) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryMatch

end OAI
end
