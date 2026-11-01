-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Bianchi_coupling_matrix_coordinates_2_2
-- name    : OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:16:09.439992+00:00
-- url     : https://prove2.me/theorems/3e940eb3-6d85-49dc-8a83-b6dc0f084639
-- title:
--   OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2` of [lean/OAI/Geometry/EinsteinFour/GeneralMatrixCompression.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeneralMatrixCompression.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Bianchi`, with `open scoped BigOperators`, `open TraceHessian PositiveEinsteinFour.Geometry`):
--
--   ```lean
--   theorem coupling_matrix_coordinates_2_2
--       (a b c d e : ℝ) (v : Fin 3 → Vec) :
--       rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 =
--         (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Bianchi.Vec`, `OAI.PositiveEinsteinFour.TraceHessian.ofCoordinates` and `OAI.PositiveEinsteinFour.Bianchi.Tensor.matrix` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.Bianchi.costParameters`, `OAI.PositiveEinsteinFour.Bianchi.generalMatrixAction`, `OAI.PositiveEinsteinFour.Bianchi.generalMixedAction` and `OAI.PositiveEinsteinFour.Bianchi.rawCoupling` (definitions bundle `OAIQ091C007` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/GeneralMatrixCompression.lean (declaration OAI.PositiveEinsteinFour.Bianchi.coupling_matrix_coordinates_2_2)

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

open scoped BigOperators
open TraceHessian PositiveEinsteinFour.Geometry

noncomputable section

theorem coupling_matrix_coordinates_2_2
    (a b c d e : ℝ) (v : Fin 3 → Vec) :
    rawCoupling (generalMatrixAction (ofCoordinates a b c d e) (costParameters v).matrix) 2 2 =
      (-(1 / 2 : ℝ)) • generalMixedAction (ofCoordinates a b c d e) (costParameters v).matrix 2 2 := by
  sorry

end
end PositiveEinsteinFour.Bianchi

end OAI
end
