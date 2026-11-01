-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_plus_2_0_3
-- name    : OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:39:39.390007+00:00
-- url     : https://prove2.me/theorems/088750e4-6eb5-430d-902d-772d3bb9ba81
-- title:
--   OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3` of [lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.TraceHessian`, with `open scoped BigOperators`, `open HighestHessian`):
--
--   ```lean
--   theorem traceLift_plus_2_0_3 (M : Mat) (a b : Fin 3) :
--       totalPlus 2 (traceLift M) 0 3 a b =
--         traceLift (matrixAction 2 M) 0 3 a b
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Mat` and `OAI.PositiveEinsteinFour.TraceHessian.matrixAction` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.TraceHessian.traceLift` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean (declaration OAI.PositiveEinsteinFour.TraceHessian.traceLift_plus_2_0_3)

import Mathlib
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.TraceHessian

noncomputable section

open scoped BigOperators
open HighestHessian
set_option maxHeartbeats 1000000

theorem traceLift_plus_2_0_3 (M : Mat) (a b : Fin 3) :
    totalPlus 2 (traceLift M) 0 3 a b =
      traceLift (matrixAction 2 M) 0 3 a b := by
  sorry

end
end PositiveEinsteinFour.TraceHessian

end OAI
end
