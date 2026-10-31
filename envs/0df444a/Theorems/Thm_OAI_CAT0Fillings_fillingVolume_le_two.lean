-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_fillingVolume_le_two
-- name    : OAI.CAT0Fillings.fillingVolume_le_two
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:54:40.391455+00:00
-- url     : https://prove2.me/theorems/cf54bc19-8cb8-42ed-b269-7777658604e5
-- title:
--   OAI.CAT0Fillings.fillingVolume_le_two: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.fillingVolume_le_two` of [lean/OAI/Geometry/CAT0Fillings/Fillings/Compact.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Compact.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal ENNReal`):
--
--   ```lean
--   theorem fillingVolume_le_two (hX : IsCAT0 X)
--       {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0) :
--       fillingVolume T ≤ fillingCoefficient 2*(mass T)^fillingPower 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.boundarySucc`, `OAI.CAT0Fillings.fillingCoefficient`, `OAI.CAT0Fillings.fillingPower` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proof of `OAI.CAT0Fillings.sharp_integral_filling` of this split imports it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Compact.lean (declaration OAI.CAT0Fillings.fillingVolume_le_two)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal ENNReal

namespace CAT0Fillings
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem fillingVolume_le_two (hX : IsCAT0 X)
    {T : Functional X 2} (hT : IsIntegral 2 T) (hz : boundarySucc T = 0) :
    fillingVolume T ≤ fillingCoefficient 2*(mass T)^fillingPower 2 := by
  sorry

end CAT0Fillings
end

end OAI
end
