-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_HighestHessian_totalPlus_highest
-- name    : OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:44:31.013521+00:00
-- url     : https://prove2.me/theorems/8b256902-ea00-4679-8fef-538787c23918
-- title:
--   OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest` of [lean/OAI/Geometry/EinsteinFour/HighestActionCoordinates.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestActionCoordinates.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.HighestHessian`, with `open scoped BigOperators`, `open Bianchi TraceHessian`):
--
--   ```lean
--   theorem totalPlus_highest (s : Fin 3) (c : Fin 21 → ℝ) :
--       totalPlus s (highest c) = highest (plusCoordinates s c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.HighestHessian.highest` and `OAI.PositiveEinsteinFour.TraceHessian.Hessian` (definitions bundle `OAIQ091C000` of this split); `OAI.PositiveEinsteinFour.HighestHessian.plusCoordinates` (definitions bundle `OAIQ091C004` of this split); `OAI.PositiveEinsteinFour.HighestHessian.totalPlus` (definitions bundle `OAIQ091C015` of this split).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_HighestHessian_coupledOperator_of_condition`, `OAI.PositiveEinsteinFour.HighestHessian.generalCurvaturePairing_highestProjection`, `OAI.PositiveEinsteinFour.HighestHessian.general_highestProjection_curvature_le`, `OAI.PositiveEinsteinFour.HighestHessian.highestProjection_plusPolynomial`, `OAI_PositiveEinsteinFour_HighestHessian_totalPlus_condition` and `OAI.PositiveEinsteinFour.HighestHessian.totalPlus_energy_of_condition` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/HighestActionCoordinates.lean (declaration OAI.PositiveEinsteinFour.HighestHessian.totalPlus_highest)

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

theorem totalPlus_highest (s : Fin 3) (c : Fin 21 → ℝ) :
    totalPlus s (highest c) = highest (plusCoordinates s c) := by
  sorry

end
end PositiveEinsteinFour.HighestHessian

end OAI
end
