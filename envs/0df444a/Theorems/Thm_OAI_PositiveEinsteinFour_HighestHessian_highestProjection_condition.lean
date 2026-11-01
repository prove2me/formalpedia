-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_highestProjection_condition
-- name    : OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:42:18.254848+00:00
-- url     : https://prove2.me/theorems/c0752a69-7104-4df7-bf3b-26279a196e50
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition` of [lean/OAI/Geometry/EinsteinFour/HighestProjection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestProjection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Bianchi TraceHessian`):
--
--   ```lean
--   theorem highestProjection_condition (X : Hessian) : condition (highestProjection X)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.TraceHessian.Hessian` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.condition` and `OAI.PositiveEinsteinFour.HighestHessian.highestProjection` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le` and `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_plusPolynomial` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestProjection.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.highestProjection_condition)

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

theorem highestProjection_condition (X : Hessian) : condition (highestProjection X) := by
  sorry

end
end PositiveEinsteinFour.HighestHessian

end OAI
end
