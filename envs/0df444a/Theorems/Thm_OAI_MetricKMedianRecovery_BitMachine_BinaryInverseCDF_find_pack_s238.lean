-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInverseCDF_find_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:59:51.004318+00:00
-- url     : https://prove2.me/theorems/f86b0b13-be4f-453a-8d52-c3c082918551
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes )`, `open Dyadic.Canonical`):
--
--   ```lean
--   lemma find_pack_s238 (ws : List ℕ) (v : ℕ) :
--       find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.encodeOption` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.Dyadic.Canonical.rank` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.BitMachine.NaturalArray.encode` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find` (definitions bundle `Q238K037` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRefinedRecovery`).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238` and `OAI_MetricKMedianRecovery_BitMachine_BinarySampler_Loop_step_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack)

import Mathlib
import Definitions.Def_KMedianRefinedRecovery
import Definitions.Def_Q238K037

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryInverseCDF
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field field_computes )
open Dyadic.Canonical

attribute [local irreducible] Take.run UnaryResources.inc
attribute [local irreducible] prefixCounts NaturalArray.sumWords
attribute [local irreducible] total
lemma find_pack_s238 (ws : List ℕ) (v : ℕ) :
    find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v) := by
  sorry

attribute [local irreducible] searched
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

end OAI
end
