-- Prove2me | Theorems.Thm_OAI_PlanarFalconer_PositiveDistanceData_normalizedHighShellF_measurable
-- name    : OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T08:52:40.614985+00:00
-- url     : https://prove2.me/theorems/aa47fa9e-2e7f-4d19-b6f6-ce35d7b899d2
-- title:
--   OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable: intermediate lemma from OpenAI, The Falconer distance conjecture in all dimensions (result family 073)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFalconer.mainTarget_proved`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Falconer distance conjecture in all dimensions (result family 073)*, OpenAI Math Release, September 23, 2026, result family 73, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable` of [lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMeasurable.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMeasurable.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFalconer.PositiveDistanceData`, with `open MeasureTheory`):
--
--   ```lean
--   theorem normalizedHighShellF_measurable (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
--       (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (n : ℕ) (v : ℝ) :
--       Measurable (d.normalizedHighShellF n v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFalconer.PositiveDistanceData`, `OAI.PlanarFalconer.DyadicSquare`, `OAI.PlanarFalconer.PositiveDistanceData.StronglySeparated` and `OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF` (definitions bundle `OAIQ038F000` of this split); `OAI.PlanarFalconer.Plane` (the published bundle `Def_PlanarFalconer`).
--
--   **Used by.** The proof of `OAI.PlanarFalconer.PositiveDistanceData.uniform_high_shell_parent_bound` of this split imports it.
-- source:
--   OpenAI, The Falconer distance conjecture in all dimensions (result family 073), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 73; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Falconer-distance-conjecture-in-all-dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MeasureTheory/Falconer/Falconer/Shells/HighShellMeasurable.lean (declaration OAI.PlanarFalconer.PositiveDistanceData.normalizedHighShellF_measurable)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F000

section

attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
namespace PositiveDistanceData

theorem normalizedHighShellF_measurable (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (n : ℕ) (v : ℝ) :
    Measurable (d.normalizedHighShellF n v) := by
  sorry

end PositiveDistanceData

end PlanarFalconer

end OAI
end
