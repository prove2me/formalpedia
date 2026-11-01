-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_energy_of_condition
-- name    : OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:45:03.829826+00:00
-- url     : https://prove2.me/theorems/cfd3f793-e6a2-4618-848c-5ccb140a1f4d
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition` of [lean/OAI/Geometry/EinsteinFour/HighestAction.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestAction.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Bianchi TraceHessian`):
--
--   ```lean
--   theorem totalPlus_energy_of_condition (X : Hessian) (hX : condition X) :
--       hessianNormSq (totalPlus 0 X) + hessianNormSq (totalPlus 1 X) +
--         hessianNormSq (totalPlus 2 X) = 48 * hessianNormSq X
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.TraceHessian.hessianNormSq` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.condition` and `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_HighestHessian_generalCasimirCurvatureForm_nonneg`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le` and `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestAction.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition)

import Mathlib
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.HighestHessian

noncomputable section

open scoped BigOperators
open Bianchi TraceHessian

theorem totalPlus_energy_of_condition (X : Hessian) (hX : condition X) :
    hessianNormSq (totalPlus 0 X) + hessianNormSq (totalPlus 1 X) +
      hessianNormSq (totalPlus 2 X) = 48 * hessianNormSq X := by
  sorry

end
end PositiveEinsteinFour.HighestHessian

end OAI
end
