-- Prove2me | Theorems.Thm_OAI_PlanarUnitDistances_IncidenceNoise_limit
-- name    : OAI.PlanarUnitDistances.IncidenceNoise.limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T02:56:27.043992+00:00
-- url     : https://prove2.me/theorems/18715c3a-d314-482b-ab9a-b651b40a1ce3
-- title:
--   OAI.PlanarUnitDistances.IncidenceNoise.limit: intermediate lemma from OpenAI, A power saving for planar unit distances
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarUnitDistances.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A power saving for planar unit distances*, OpenAI Math Release, September 23, 2026, result family 167, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarUnitDistances.IncidenceNoise.limit` of [lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarUnitDistances.IncidenceNoise`, with `open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters`, `open scoped Classical`):
--
--   ```lean
--   lemma limit : Tendsto (noise s a) atTop (nhds 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarUnitDistances.BudgetParameters.Params`, `OAI.PlanarUnitDistances.IncidenceNoise.noise` and `OAI.PlanarUnitDistances.IncidenceSequence.Sequence` (definitions bundle `OAIQ2Un000` of this split).
--
--   **Used by.** The proof of `OAI.PlanarUnitDistances.IncidenceBand.choose` of this split imports it.
-- source:
--   OpenAI, A power saving for planar unit distances, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 167; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-power-saving-for-planar-unit-distances-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/UnitDistances/UnitDistances/RareBudget.lean (declaration OAI.PlanarUnitDistances.IncidenceNoise.limit)

import Mathlib
import Definitions.Def_OAIQ2Un000

section

attribute [-instance] _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instFieldK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instIsGaloisRatK _root_.OAI.PlanarUnitDistances.IncidenceDiagonal.Data.instNumberFieldK
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.IncidenceNoise
open Filter FiniteLaw FiniteStarCoupling IncidenceSequence IncidenceScale IncidenceBook BudgetParameters
open scoped Classical
noncomputable section
variable (s : Sequence) (a : Params)
lemma limit : Tendsto (noise s a) atTop (nhds 0) := by
  sorry
end
end PlanarUnitDistances.IncidenceNoise

end OAI
end
