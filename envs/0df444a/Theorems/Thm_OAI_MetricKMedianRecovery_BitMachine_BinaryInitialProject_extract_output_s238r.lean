-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInitialProject_extract_output_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:48:33.02783+00:00
-- url     : https://prove2.me/theorems/a35a1814-5b91-4a8e-b369-f74c9f2a50c9
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject`, with `open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge`, `open BinaryOpeningPayment (field field_encode)`, `open BinaryFiniteContext (labels setBits)`):
--
--   ```lean
--   lemma extract_output_s238r (o : StartOutput (Fin m)) : extract (BinaryInitial.output o)=BinaryFinSet.encode o.project
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.encode` (definitions bundle `Q238L017` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.project` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract` (definitions bundle `Q238L029` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInitial.output` (definitions bundle `Q238L030` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.run_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInitialProject.extract_output)

import Mathlib
import Definitions.Def_Q238L029
import Definitions.Def_Q238L030

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInitialProject
open WordOperations WordList BinaryArithmetic RationalLeaves CanonicalCoupledMerge
open BinaryOpeningPayment (field field_encode)
open BinaryFiniteContext (labels setBits)
variable {m d : ℕ}
attribute [local irreducible] BinaryProjection.run BinaryFiniteMachine.after
lemma extract_output_s238r (o : StartOutput (Fin m)) : extract (BinaryInitial.output o)=BinaryFinSet.encode o.project := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryInitialProject

end OAI
end
