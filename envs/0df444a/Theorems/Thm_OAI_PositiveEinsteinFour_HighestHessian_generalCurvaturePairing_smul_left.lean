-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_generalCurvaturePairing_smul_left
-- name    : OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:42:10.908791+00:00
-- url     : https://prove2.me/theorems/b9362ba3-5866-4ab2-afe9-f96bdc34d6c3
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem generalCurvaturePairing_smul_left (A U : Mat) (c : ℝ) (X Y : Hessian) :
--       generalCurvaturePairing A U (c • X) Y = c * generalCurvaturePairing A U X Y
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian` and `OAI.PositiveEinsteinFour.TraceHessian.Mat` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_hessianIntegrand_integrable`, `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_integral_regularizedHessian_tendsto`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.preVarianceGreen_oriented`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.traceGreen`, `OAI_PositiveEinsteinFour_Geometry_general_traceCorrection_weyl`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le`, `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square` and `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_trace_subtraction` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_smul_left)

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

theorem generalCurvaturePairing_smul_left (A U : Mat) (c : ℝ) (X Y : Hessian) :
    generalCurvaturePairing A U (c • X) Y = c * generalCurvaturePairing A U X Y := by
  sorry

end
end PositiveEinsteinFour.HighestHessian
end

end OAI
end
