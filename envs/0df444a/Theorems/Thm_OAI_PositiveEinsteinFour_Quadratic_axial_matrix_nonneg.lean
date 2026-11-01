-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_axial_matrix_nonneg
-- name    : OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:07:31.851639+00:00
-- url     : https://prove2.me/theorems/210b3c08-c316-4e0b-852c-f739d191ac96
-- title:
--   OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Quadratic`, with `open Potential`):
--
--   ```lean
--   theorem axial_matrix_nonneg {v b : ℝ}
--       (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ) :
--       0 ≤ A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Quadratic.A12` (definitions bundle `OAIQ091C004` of this split); `OAI.PositiveEinsteinFour.Quadratic.A11` and `OAI.PositiveEinsteinFour.Quadratic.A22` (definitions bundle `OAIQ091C012` of this split).
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_QuaternionFrame_PointwiseSpectrum_axial_closed` and `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean (declaration OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg)

import Mathlib
import Definitions.Def_OAIQ091C012

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Quadratic

open Potential

noncomputable section

theorem axial_matrix_nonneg {v b : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2) (x y : ℝ) :
    0 ≤ A11 v b 1 * x ^ 2 + 2 * A12 v b 1 * x * y + A22 v b 1 * y ^ 2 := by
  sorry

end

end PositiveEinsteinFour.Quadratic
end

end OAI
end
