-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_quadratic_form_nonneg_of_det
-- name    : OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T16:57:05.999006+00:00
-- url     : https://prove2.me/theorems/9e90569e-b67b-4282-a5a5-9b26a3dbcbab
-- title:
--   OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det` of [lean/OAI/Geometry/EinsteinFour/Matrix.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/Matrix.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour`):
--
--   ```lean
--   theorem quadratic_form_nonneg_of_det
--       (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) (hdet : s ^ 2 ≤ r * h)
--       (x y : ℝ) :
--       0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2
--   ```
--
--   **Used by.** The proofs of `OAI_PositiveEinsteinFour_Geometry_MetricGreenData_coupledIntegral_oriented`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.minusNormVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.normDifferenceVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusHVariance`, `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.plusNormVariance`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_minus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_H_plus_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_difference_variance`, `OAI_PositiveEinsteinFour_Geometry_regularized_minus_variance`, `OAI_PositiveEinsteinFour_Geometry_smooth_weighted_variance_ae`, `OAI.PositiveEinsteinFour.Quadratic.B_ACE`, `OAI.PositiveEinsteinFour.Quadratic.B_ASE`, `OAI.PositiveEinsteinFour.Quadratic.B_CBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SUB`, `OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg`, `OAI_PositiveEinsteinFour_Quadratic_coupling_matrix_nonneg`, `OAI_PositiveEinsteinFour_Quadratic_quadratic_bound_closed`, `OAI_PositiveEinsteinFour_QuaternionFrame_PointwiseSpectrum_axial_closed`, `OAI.PositiveEinsteinFour.QuaternionFrame.arrayCoupledIntegrand_le_reduced`, `OAI_PositiveEinsteinFour_QuaternionFrame_cubic_bound_of_weight_square` and `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/Matrix.lean (declaration OAI.PositiveEinsteinFour.quadratic_form_nonneg_of_det)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour

theorem quadratic_form_nonneg_of_det
    (r h s : ℝ) (hr : 0 ≤ r) (hh : 0 ≤ h) (hdet : s ^ 2 ≤ r * h)
    (x y : ℝ) :
    0 ≤ r * x ^ 2 + 2 * s * x * y + h * y ^ 2 := by
  sorry

end PositiveEinsteinFour

end OAI
end
