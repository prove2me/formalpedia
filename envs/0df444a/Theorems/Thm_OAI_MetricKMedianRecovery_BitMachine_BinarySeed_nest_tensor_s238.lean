-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinarySeed_nest_tensor_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:03:46.702179+00:00
-- url     : https://prove2.me/theorems/524805ce-ac49-4893-8c6d-2ccc9e1689a0
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/SeedTensor.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SeedTensor.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinarySeed`, with `open WordOperations WordList BinaryArithmetic`):
--
--   ```lean
--   lemma nest_tensor_s238 {ds : List ℕ} {b : ℕ} (s : Tensor ds b) :
--       nest ds.length (pairBits (shape (ds++[b]),raw s))=parsed s
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.Tensor` and `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.raw` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.parsed` and `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.shape` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest` (definitions bundle `Q238K037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.context_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchRandomize.labels_pack_s238`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.left_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.Prepare.run_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/SeedTensor.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinarySeed.nest_tensor)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinarySeed
open WordOperations WordList BinaryArithmetic
attribute [local irreducible] width RawTake.run RawDrop.run
lemma nest_tensor_s238 {ds : List ℕ} {b : ℕ} (s : Tensor ds b) :
    nest ds.length (pairBits (shape (ds++[b]),raw s))=parsed s := by
  sorry
end MetricKMedianRecovery.BitMachine.BinarySeed

end OAI
end
