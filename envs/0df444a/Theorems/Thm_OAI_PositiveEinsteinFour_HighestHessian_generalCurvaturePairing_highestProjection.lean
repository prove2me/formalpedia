-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_highestProjection
-- name    : OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:38:50.052431+00:00
-- url     : https://prove2.me/theorems/fd3b9d40-e0db-4e66-b739-c6c4bc38b97d
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem generalCurvaturePairing_highestProjection (A U : Mat) (X L : Hessian)
--       (hX : condition X) :
--       generalCurvaturePairing A U X (highestProjection L) = generalCurvaturePairing A U X L
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian` and `OAI.PositiveEinsteinFour.TraceHessian.Mat` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.condition`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing` and `OAI.PositiveEinsteinFour.HighestHessian.highestProjection` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le` and `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ091C015

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.HighestHessian

open scoped BigOperators
open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction

noncomputable section

theorem generalCurvaturePairing_highestProjection (A U : Mat) (X L : Hessian)
    (hX : condition X) :
    generalCurvaturePairing A U X (highestProjection L) = generalCurvaturePairing A U X L := by
  sorry

end
end PositiveEinsteinFour.HighestHessian
end

end OAI
end
