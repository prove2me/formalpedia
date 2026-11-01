-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_TraceHessian_totalMinus_traceLift
-- name    : OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:47:57.938932+00:00
-- url     : https://prove2.me/theorems/c9d6314c-1a69-4346-a476-1ba90706f10a
-- title:
--   OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift` of [lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.TraceHessian`, with `open scoped BigOperators`, `open HighestHessian`):
--
--   ```lean
--   theorem totalMinus_traceLift (s : Fin 3) (M : Mat) :
--       totalMinus s (traceLift M) = 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian` and `OAI.PositiveEinsteinFour.TraceHessian.Mat` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.TraceHessian.traceLift` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalMinus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen`, `OAI_PositiveEinsteinFour_Geometry_general_traceCorrection_weyl` and `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/TraceActionIntertwining.lean (declaration OAI.PositiveEinsteinFour.TraceHessian.totalMinus_traceLift)

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

theorem totalMinus_traceLift (s : Fin 3) (M : Mat) :
    totalMinus s (traceLift M) = 0 := by
  sorry

end
end PositiveEinsteinFour.TraceHessian

end OAI
end
