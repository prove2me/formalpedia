-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryInverseCDF_find_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:58:07.794541+00:00
-- url     : https://prove2.me/theorems/e5954367-642c-46c7-955e-896f9f7c663b
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field field_computes )`, `open Dyadic.Canonical`):
--
--   ```lean
--   lemma find_pack_s238r (ws : List ℕ) (v : ℕ) :
--       find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.encodeOption` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.Dyadic.Canonical.rank` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.BitMachine.NaturalArray.encode` (definitions bundle `Q238L020` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find` (definitions bundle `Q238L034` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryDyadic.lookup_draw_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Sampling/InverseCDF.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryInverseCDF.find_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L034

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
lemma find_pack_s238r (ws : List ℕ) (v : ℕ) :
    find (pairBits (NaturalArray.encode ws,v.bits))=encodeOption (rank ws v) := by
  sorry

attribute [local irreducible] searched
end MetricKMedianRecovery.BitMachine.BinaryInverseCDF

end OAI
end
