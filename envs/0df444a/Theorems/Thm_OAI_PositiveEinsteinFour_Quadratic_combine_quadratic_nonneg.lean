-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_combine_quadratic_nonneg
-- name    : OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T16:57:27.026003+00:00
-- url     : https://prove2.me/theorems/38f3b782-bb16-456d-8951-85434b093f22
-- title:
--   OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Quadratic`):
--
--   ```lean
--   theorem combine_quadratic_nonneg (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ)
--       (h : L.Forall (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)) :
--       0 ≤ (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
--         2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
--         (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2
--   ```
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Quadratic.B_ACE`, `OAI.PositiveEinsteinFour.Quadratic.B_ASE`, `OAI.PositiveEinsteinFour.Quadratic.B_CBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SBE`, `OAI.PositiveEinsteinFour.Quadratic.B_SUB`, `OAI.PositiveEinsteinFour.Quadratic.axial_matrix_nonneg` and `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean (declaration OAI.PositiveEinsteinFour.Quadratic.combine_quadratic_nonneg)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace PositiveEinsteinFour.Quadratic

noncomputable section

theorem combine_quadratic_nonneg (L : List (ℝ × ℝ × ℝ × ℝ)) (x y : ℝ)
    (h : L.Forall (fun a => 0 ≤ (a.1 * x ^ 2 + 2 * a.2.2.1 * x * y + a.2.1 * y ^ 2) * a.2.2.2)) :
    0 ≤ (L.map (fun a => a.1 * a.2.2.2)).sum * x ^ 2 +
      2 * (L.map (fun a => a.2.2.1 * a.2.2.2)).sum * x * y +
      (L.map (fun a => a.2.1 * a.2.2.2)).sum * y ^ 2 := by
  sorry

end

end PositiveEinsteinFour.Quadratic
end

end OAI
end
