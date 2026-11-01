-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_general_weighted_highestProjection_square
-- name    : OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:41:49.312169+00:00
-- url     : https://prove2.me/theorems/01a5aa05-4cf1-493d-9a1a-0b587b6f25da
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Matrix Bianchi TraceHessian PositiveEinsteinFour.Geometry CurvatureContraction`):
--
--   ```lean
--   theorem general_weighted_highestProjection_square (A U : Mat)
--       (hA : symmetric A) (hU : symmetric U) (X L : Hessian) (hX : condition X)
--       (x y m : ℝ) (hm : 0 < m)
--       (hAx : (A + x • (1 : Mat)).PosSemidef)
--       (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
--       0 ≤ (m / 6) * generalCurvaturePairing A U X X +
--         generalCurvaturePairing A U X L / 6 +
--         generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian`, `OAI.PositiveEinsteinFour.TraceHessian.Mat` and `OAI.PositiveEinsteinFour.TraceHessian.symmetric` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.condition`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing` and `OAI.PositiveEinsteinFour.HighestHessian.highestProjection` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.localWeightedHessian` and `OAI_PositiveEinsteinFour_HighestHessian_general_local_weighted_original_square` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates01.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.general_weighted_highestProjection_square)

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

theorem general_weighted_highestProjection_square (A U : Mat)
    (hA : symmetric A) (hU : symmetric U) (X L : Hessian) (hX : condition X)
    (x y m : ℝ) (hm : 0 < m)
    (hAx : (A + x • (1 : Mat)).PosSemidef)
    (hUy : (U + y • (1 : Mat)).PosSemidef) (hxy : x + y ≤ 2) :
    0 ≤ (m / 6) * generalCurvaturePairing A U X X +
      generalCurvaturePairing A U X L / 6 +
      generalCurvaturePairing A U (highestProjection L) (highestProjection L) / (24 * m) := by
  sorry

end
end PositiveEinsteinFour.HighestHessian
end

end OAI
end
