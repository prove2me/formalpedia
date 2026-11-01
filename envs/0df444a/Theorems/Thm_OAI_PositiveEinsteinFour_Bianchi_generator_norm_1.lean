-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_generator_norm_1
-- name    : OAI.PositiveEinsteinFour.Bianchi.generator_norm_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:03:39.935959+00:00
-- url     : https://prove2.me/theorems/b7ab82fb-2299-4fe4-99fc-334dc73fd290
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.generator_norm_1: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.generator_norm_1` of [lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian`):
--
--   ```lean
--   theorem generator_norm_1 (v : Fin 3 → Vec) :
--       coordinateNorm (generatorCoordinates 1 v) =
--         170 * ‖v 0‖ ^ 2 + 190 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
--         (-320) * inner ℝ (v 0) (v 1) + (80) * inner ℝ (v 0) (v 2) +
--         (-80) * inner ℝ (v 1) (v 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Vec` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.coordinateNorm` and `OAI.PositiveEinsteinFour.Bianchi.generatorCoordinates` (definitions bundle `OAIQ091C007` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.Bianchi.costCoefficient_norm` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GradientCoordinateModel.lean (declaration OAI.PositiveEinsteinFour.Bianchi.generator_norm_1)

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

theorem generator_norm_1 (v : Fin 3 → Vec) :
    coordinateNorm (generatorCoordinates 1 v) =
      170 * ‖v 0‖ ^ 2 + 190 * ‖v 1‖ ^ 2 + 70 * ‖v 2‖ ^ 2 +
      (-320) * inner ℝ (v 0) (v 1) + (80) * inner ℝ (v 0) (v 2) +
      (-80) * inner ℝ (v 1) (v 2) := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end OAI
end
