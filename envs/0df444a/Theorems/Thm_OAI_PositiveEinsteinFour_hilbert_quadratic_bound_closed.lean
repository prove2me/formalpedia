-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_hilbert_quadratic_bound_closed
-- name    : OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:10:38.583684+00:00
-- url     : https://prove2.me/theorems/25167db8-b02f-4946-9613-a8f172aff6cc
-- title:
--   OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour`, with `open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential`):
--
--   ```lean
--   theorem hilbert_quadratic_bound_closed
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
--       (p q : E) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
--       quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
--         quadraticCoefficient b v * ‖q‖ ^ 2 ≤
--         2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.Potential.theta` (definitions bundle `OAIQ091C001` of this split); `OAI.PositiveEinsteinFour.normWeight` (definitions bundle `OAIQ091C004` of this split); `OAI.PositiveEinsteinFour.Quadratic.mixedCoefficient` and `OAI.PositiveEinsteinFour.Quadratic.quadraticCoefficient` (definitions bundle `OAIQ091C012` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.reduced_integrand_bound` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean (declaration OAI.PositiveEinsteinFour.hilbert_quadratic_bound_closed)

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

namespace PositiveEinsteinFour

open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential

noncomputable section

theorem hilbert_quadratic_bound_closed
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b : ℝ} (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (p q : E) (hp : v = 0 → p = 0) (hq : b = 0 → q = 0) :
    quadraticCoefficient v b * ‖p‖ ^ 2 + 2 * mixedCoefficient v b * inner ℝ p q +
      quadraticCoefficient b v * ‖q‖ ^ 2 ≤
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) := by
  sorry

end
end PositiveEinsteinFour
end

end OAI
end
