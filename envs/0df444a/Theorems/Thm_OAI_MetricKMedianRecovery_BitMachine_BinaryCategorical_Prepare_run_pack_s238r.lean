-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_Prepare_run_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:56:18.933357+00:00
-- url     : https://prove2.me/theorems/e504aab4-6008-42b6-81eb-de1a705eb98c
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRawPrep.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRawPrep.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes )`, `open Categorical.Explicit`):
--
--   ```lean
--   lemma run_pack_s238r : run xx=outputPack ctx part (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.BinaryOracleIndex`, `OAI.MetricKMedianRecovery.Categorical.OracleSeed`, `OAI.MetricKMedianRecovery.Categorical.binarySeedEquiv`, `OAI.MetricKMedianRecovery.Categorical.Explicit.exponent` and `OAI.MetricKMedianRecovery.Categorical.Explicit.samples` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.outputPack` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.pack` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run` (definitions bundle `Q238L034` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.run_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryZeroBranch.run_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalRawPrep.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack)

import Mathlib
import Definitions.Def_Q238L034

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Categorical.Explicit
variable {q a : ℕ}
attribute [local irreducible] Resources.tword Resources.lword Resources.bword dimensions
attribute [local irreducible] BinarySeed.product leftShape
attribute [local irreducible] BinarySeed.nest RawTake.run RawDrop.run cut rightShape tword lword bword
section Correct
variable (ctx : List Bool) (part : Fin q→Fin a)
  (bits : Categorical.BinaryOracleIndex (Fin q) a (exponent a) (samples q a)→Bool)
local notation "xx" => pack ctx part bits
lemma run_pack_s238r : run xx=outputPack ctx part (Categorical.binarySeedEquiv (Fin q) a (exponent a) (samples q a) bits) := by
  sorry
end Correct
end MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare

end OAI
end
