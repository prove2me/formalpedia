-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_coordinates
-- name    : OAI.PositiveEinsteinFour.Bianchi.generator_coordinates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:00:50.405928+00:00
-- url     : https://prove2.me/theorems/16faf24f-92e1-49a6-b23f-55ee3005f1b4
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.generator_coordinates: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.generator_coordinates` of [lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian`):
--
--   ```lean
--   theorem generator_coordinates (s : Fin 3) (v : Fin 3 → Vec) :
--       rawGradientGenerator s (costParameters v).matrix =
--         (costParameters (generatorCoordinates s v)).matrix
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.RawGradient`, `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.Bianchi.rawGradientGenerator` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.matrix` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.costParameters` and `OAI.PositiveEinsteinFour.Bianchi.generatorCoordinates` (definitions bundle `OAIQ091C007` of this split).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_coordinates`, `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_norm`, `OAI_PositiveEinsteinFour_Bianchi_rawCostCoefficient_pairing`, `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_bianchi`, `OAI.PositiveEinsteinFour.Bianchi.totalGradientTensor_matrix`, `OAI.PositiveEinsteinFour.Bianchi.totalPlus_weightPlusPart_generalCost`, `OAI_PositiveEinsteinFour_Bianchi_totalPlus_weightPlusPart_pairing`, `OAI.PositiveEinsteinFour.Bianchi.weightPlusPart_plus_energy`, `OAI_PositiveEinsteinFour_HighestHessian_general_innerAction_energy` and `OAI_PositiveEinsteinFour_HighestHessian_general_plus_energy` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean (declaration OAI.PositiveEinsteinFour.Bianchi.generator_coordinates)

import Mathlib
import Definitions.Def_OAIQ091C007

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.Bianchi

noncomputable section

open scoped BigOperators
open TraceHessian
set_option maxHeartbeats 1000000

theorem generator_coordinates (s : Fin 3) (v : Fin 3 → Vec) :
    rawGradientGenerator s (costParameters v).matrix =
      (costParameters (generatorCoordinates s v)).matrix := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end OAI
end
