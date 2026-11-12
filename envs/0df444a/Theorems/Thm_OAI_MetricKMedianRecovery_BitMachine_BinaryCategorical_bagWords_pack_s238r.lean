-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_bagWords_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:37:33.328988+00:00
-- url     : https://prove2.me/theorems/502aed34-6228-4702-a399-f77431437405
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma bagWords_pack_s238r (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
--       (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
--       bagWords (pairBits (scorePack ctx part r seed,j.val.bits))=
--         encode ((Categorical.Selected.bag (elements q) part j).map elemBits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Categorical.OracleSeed`, `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elements` and `OAI.MetricKMedianRecovery.Categorical.Selected.bag` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.elemBits` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.scorePack` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords` (definitions bundle `Q238L024` of this split); `OAI.MetricKMedianRecovery.pairBits` (the published bundle `Def_KMedianRecovery`).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.choose_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalChoice.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.bagWords_pack)

import Mathlib
import Definitions.Def_KMedianRecovery
import Definitions.Def_Q238L019
import Definitions.Def_Q238L024

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {q a T L : ℕ}
lemma bagWords_pack_s238r (ctx : List Bool) (part : Fin q→Fin a) (r : Fin a→Fin T→Option (Fin q))
    (seed : Categorical.OracleSeed (Fin q) a T L) (j : Fin a) :
    bagWords (pairBits (scorePack ctx part r seed,j.val.bits))=
      encode ((Categorical.Selected.bag (elements q) part j).map elemBits) := by
  sorry
attribute [local irreducible] mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end
