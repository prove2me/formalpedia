-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryBlueLoop_run_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:46:16.447201+00:00
-- url     : https://prove2.me/theorems/dfbcd0d7-fd18-4d31-b39b-283fb46e2ce0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueTableSize.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueTableSize.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop`, with `open WordOperations WordList`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma run_pack_s238 (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
--       (U : Finset (Fin m)) (c : ℕ) : run (pack er B F label q U c)=
--         BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BlueDP.Atom` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueCell.atomEnc`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueChoice.encode`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.pack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueMerge.listEnc` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.BlueDP.best` and `OAI.MetricKMedianRecovery.BlueDP.block` (definitions bundle `Q238K011` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run` (definitions bundle `Q238K029` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.plan_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryObservableBranch.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/BlueTableSize.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryBlueLoop.run_pack)

import Mathlib
import Definitions.Def_Q238K029

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBlueLoop
open WordOperations WordList
open BinaryOpeningPayment (field )
variable {n m : ℕ} {R : Type*} [LinearOrder R]
lemma run_pack_s238 (er : R→List Bool) (B : Finset R) (F : Finset (Fin n)) (label : R→Fin m) (q : R→Fin n→ℚ)
    (U : Finset (Fin m)) (c : ℕ) : run (pack er B F label q U c)=
      BinaryBlueChoice.encode (BinaryBlueMerge.listEnc (BinaryBlueCell.atomEnc er)) (BlueDP.best (BlueDP.block B F label q) c U) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryBlueLoop

end OAI
end
