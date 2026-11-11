-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_draw_pack_s238
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:26:02.91173+00:00
-- url     : https://prove2.me/theorems/eb33fcb4-8390-4881-8fde-83ab0c534979
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical`, with `open WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma draw_pack_s238 (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
--       draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238K001` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawn` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.omitted` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPack` (definitions bundle `Q238K013` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw` (definitions bundle `Q238K020` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack)

import Mathlib
import Definitions.Def_Q238K013
import Definitions.Def_Q238K020

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCategorical
open WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {E : Type*} {a T : ℕ}
lemma draw_pack_s238 (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc) := by
  sorry
attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end
