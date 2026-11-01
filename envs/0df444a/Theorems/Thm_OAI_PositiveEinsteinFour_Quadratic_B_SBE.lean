-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Quadratic_B_SBE
-- name    : OAI.PositiveEinsteinFour.Quadratic.B_SBE
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:21:21.385022+00:00
-- url     : https://prove2.me/theorems/72e799c6-3130-400c-a535-7b3eb858caec
-- title:
--   OAI.PositiveEinsteinFour.Quadratic.B_SBE: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Quadratic.B_SBE` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Quadratic`, with `open Potential`):
--
--   ```lean
--   theorem B_SBE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
--       (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 - z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 - z) / 2) * x * y + Hdiag ((1 - z) / 2) (1 + w / 2) * y ^ 2
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Quadratic.Hdiag` and `OAI.PositiveEinsteinFour.Quadratic.Hmixed` (definitions bundle `OAIQ091C012` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean (declaration OAI.PositiveEinsteinFour.Quadratic.B_SBE)

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

theorem B_SBE {z w : ℝ} (hz : 0 ≤ z) (hw : 0 ≤ w)
    (hsum : z + w ≤ 1) (x y : ℝ) : 0 ≤ Hdiag (1 + w / 2) ((1 - z) / 2) * x ^ 2 + 2 * Hmixed (1 + w / 2) ((1 - z) / 2) * x * y + Hdiag ((1 - z) / 2) (1 + w / 2) * y ^ 2 := by
  sorry

end

end PositiveEinsteinFour.Quadratic
end

end OAI
end
