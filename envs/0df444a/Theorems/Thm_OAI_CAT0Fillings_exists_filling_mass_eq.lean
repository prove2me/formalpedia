-- Prove2me | Theorems.Thm_OAI_CAT0Fillings_exists_filling_mass_eq
-- name    : OAI.CAT0Fillings.exists_filling_mass_eq
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T02:52:46.418804+00:00
-- url     : https://prove2.me/theorems/8bb53a7c-b134-4fd6-9bdc-45aa787a23e7
-- title:
--   OAI.CAT0Fillings.exists_filling_mass_eq: intermediate lemma from OpenAI, Sharp integral fillings in CAT(0) spaces
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CAT0Fillings.sharp_integral_filling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sharp integral fillings in CAT(0) spaces*, OpenAI Math Release, September 23, 2026, result family 337, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CAT0Fillings.exists_filling_mass_eq` of [lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CAT0Fillings`, with `open Set Filter MeasureTheory Metric`, `open scoped Topology NNReal`, `open Foundations Slicing`):
--
--   ```lean
--   theorem exists_filling_mass_eq (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
--       (hex : ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T) :
--       ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
--         mass S = fillingVolume T
--   ```
--
--   **Definitions.** The statement is written with `OAI.CAT0Fillings.fillingVolume` (definitions bundle `OAIQ29C0002` of this split); `OAI.CAT0Fillings.Functional`, `OAI.CAT0Fillings.IsCAT0`, `OAI.CAT0Fillings.IsIntegral`, `OAI.CAT0Fillings.boundarySucc` and `OAI.CAT0Fillings.mass` (the published bundle `Def_SharpCAT0Filling`).
--
--   **Used by.** The proofs of `OAI.CAT0Fillings.fillingVolume_le_two` and `OAI.CAT0Fillings.sharp_integral_filling` of this split import it.
-- source:
--   OpenAI, Sharp integral fillings in CAT(0) spaces, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 337; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-integral-fillings-in-CAT(0)-spaces-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/CAT0Fillings/Fillings/Attainment.lean (declaration OAI.CAT0Fillings.exists_filling_mass_eq)

import Mathlib
import Definitions.Def_SharpCAT0Filling
import Definitions.Def_OAIQ29C0002

section

attribute [-instance] _root_.OAI.CAT0Fillings.BorelCoefficients.coefficientList_nonempty _root_.OAI.CAT0Fillings.ChartGeometry.atlasMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.coordinateMeasure_finite _root_.OAI.CAT0Fillings.ChartGeometry.sobolev_separable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace CAT0Fillings
open Foundations Slicing

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [Nonempty X]

theorem exists_filling_mass_eq (hX : IsCAT0 X) {k : ℕ} {T : Functional X (k+1)}
    (hex : ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T) :
    ∃ S : Functional X (k+2), IsIntegral (k+2) S ∧ boundarySucc S = T ∧
      mass S = fillingVolume T := by
  sorry

end CAT0Fillings
end

end OAI
end
