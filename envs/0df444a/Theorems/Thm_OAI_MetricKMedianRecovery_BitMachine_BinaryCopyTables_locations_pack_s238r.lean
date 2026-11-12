-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_BitMachine_BinaryCopyTables_locations_pack_s238r
-- name    : OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:43:43.04721+00:00
-- url     : https://prove2.me/theorems/f2c60e8e-f83d-44ac-8097-1bf1162a6994
-- title:
--   OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack` of [lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyGround.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyGround.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables`, with `open WordOperations WordList BinaryArithmetic`, `open BinaryOpeningPayment (field )`):
--
--   ```lean
--   lemma locations_pack_s238r (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) :
--       locations (pack H)=BinaryFinSet.table (Completion.CopyGround.location H hH)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.Completion.CopyGround.location` (definitions bundle `Q238L002` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryFinSet.table` (definitions bundle `Q238L018` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.pack` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations` (definitions bundle `Q238L028` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryBranchContext.locations_pack_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Branching/CopyGround.lean (declaration OAI.MetricKMedianRecovery.BitMachine.BinaryCopyTables.locations_pack)

import Mathlib
import Definitions.Def_Q238L025
import Definitions.Def_Q238L028

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryCopyTables
open WordOperations WordList BinaryArithmetic
open BinaryOpeningPayment (field )
variable {n a : ℕ}
attribute [local irreducible] mapWith flatMapWith
lemma locations_pack_s238r (H : Fin a→Finset (Fin n)) (hH : ∀ i,(H i).Nonempty) :
    locations (pack H)=BinaryFinSet.table (Completion.CopyGround.location H hH) := by
  sorry
end MetricKMedianRecovery.BitMachine.BinaryCopyTables

end OAI
end
