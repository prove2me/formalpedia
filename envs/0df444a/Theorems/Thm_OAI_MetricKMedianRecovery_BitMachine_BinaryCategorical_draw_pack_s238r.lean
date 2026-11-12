-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCategorical_draw_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:37:45.636242+00:00
-- url     : https://prove2.me/theorems/e69ea505-ed33-4cea-8694-c345087d7f71
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma draw_pack_s238r (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
--       draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawn` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.omitted` (definitions bundle `Q238L003` of this split); `OAI.MetricKMedianRecovery.BitMachine.WordList.encode` (definitions bundle `Q238L006` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.drawPack` (definitions bundle `Q238L019` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw` (definitions bundle `Q238L024` of this split).
--
--   **Used by.** The proofs of `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.marginal_pack_s238r` and `OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.output_pack_s238r` of this split import it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CategoricalTable.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCategorical.draw_pack)

import Mathlib
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
variable {E : Type*} {a T : ℕ}
lemma draw_pack_s238r (enc : E→List Bool) (r : Fin a→Fin T→Option E) (s : Fin a→Fin T) (skip : ℕ) :
    draw (drawPack enc r s skip)=encode ((drawn (omitted r skip) s).map enc) := by
  sorry
attribute [local irreducible] Set.run mapWith
end MetricKMedianRecovery.BitMachine.BinaryCategorical

end OAI
end
