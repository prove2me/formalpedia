-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_traceLift_minus_2_1
-- name    : OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T18:26:50.074692+00:00
-- url     : https://prove2.me/theorems/fe5404cc-87c4-484e-ada0-89a4c609dca4
-- title:
--   OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1` of [lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.TraceHessian`, with `open scoped BigOperators`, `open HighestHessian`):
--
--   ```lean
--   theorem traceLift_minus_2_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
--       totalMinus 2 (traceLift M) 1 j a b = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Mat` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.TraceHessian.traceLift` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalMinus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean (declaration OAI.PositiveEinsteinFour.TraceHessian.traceLift_minus_2_1)

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

theorem traceLift_minus_2_1 (M : Mat) (j : Fin 4) (a b : Fin 3) :
    totalMinus 2 (traceLift M) 1 j a b = 0 := by
  sorry

end
end PositiveEinsteinFour.TraceHessian

end OAI
end
