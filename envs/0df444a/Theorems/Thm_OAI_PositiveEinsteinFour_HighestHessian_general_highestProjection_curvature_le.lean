-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_highestProjection_curvature_le
-- name    : OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:40:26.97243+00:00
-- url     : https://prove2.me/theorems/4992b9b2-c114-47da-9ff0-4d072ed5c334
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem general_highestProjection_curvature_le (A U : Mat) (hA : symmetric A)
--       (hU : symmetric U) (x y : ℝ) (hy : 0 ≤ y)
--       (hAx : (A + x • (1 : Mat)).PosSemidef)
--       (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
--       (W : Hessian) (hp : (∑ r, hessianNormSq (totalPlus r W)) = 48 * hessianNormSq W) :
--       generalCurvaturePairing A U (highestProjection W) (highestProjection W) ≤
--         generalCurvaturePairing A U W W
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian`, `OAI.PositiveEinsteinFour.TraceHessian.Mat` and `OAI.PositiveEinsteinFour.TraceHessian.symmetric` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.TraceHessian.hessianNormSq` (definitions bundle `OAIQ091C010` of this split); `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection` and `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced` and `OAI_PositiveEinsteinFour_QuaternionFrame_projection_bound_of_weight_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le)

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

theorem general_highestProjection_curvature_le (A U : Mat) (hA : symmetric A)
    (hU : symmetric U) (x y : ℝ) (hy : 0 ≤ y)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2)
    (W : Hessian) (hp : (∑ r, hessianNormSq (totalPlus r W)) = 48 * hessianNormSq W) :
    generalCurvaturePairing A U (highestProjection W) (highestProjection W) ≤
      generalCurvaturePairing A U W W := by
  sorry

end
end PositiveEinsteinFour.HighestHessian
end

end OAI
end
