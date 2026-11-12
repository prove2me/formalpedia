-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryJump_view_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:00.980354+00:00
-- url     : https://prove2.me/theorems/d4d24d88-dd21-4939-9431-388315942572
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryJump`, with `open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic`, `open BinaryFiniteContext (labels setBits)`, `open BinaryOpeningPayment (field field_computes field_encode)`):
--
--   ```lean
--   lemma view_pack_s238r {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
--       (H G : List (Label (Fin m))) : view (ctxBits F R key H G)=
--         Find.optionEncode ((CanonicalMergeRefinement.view F R (copy key) H G).map jumpBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.Jump` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.Find.optionEncode` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeRefinement.view` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.copy` and `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.jumpBits` (definitions bundle `Q238L026` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.ctxBits` (definitions bundle `Q238L030` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view` (definitions bundle `Q238L034` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryRefine.cutOp_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CrossCount.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryJump.view_pack)

import Mathlib
import Definitions.Def_Q238L030
import Definitions.Def_Q238L034

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryJump
open WordOperations WordList RationalLeaves CanonicalMergeRefinement BinaryArithmetic
open BinaryFiniteContext (labels setBits)
open BinaryOpeningPayment (field field_computes field_encode)
attribute [local irreducible] removedTail
lemma view_pack_s238r {m : ℕ} (F : Finset (Label (Fin m))) (R : List (Label (Fin m))) (key : ℕ)
    (H G : List (Label (Fin m))) : view (ctxBits F R key H G)=
      Find.optionEncode ((CanonicalMergeRefinement.view F R (copy key) H G).map jumpBits) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryJump

end OAI
end
