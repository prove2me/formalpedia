-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_Boundary_zeroOrder_bound
-- name    : OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T16:57:56.16628+00:00
-- url     : https://prove2.me/theorems/77aa72f6-ebdb-4460-811a-ee4be1c8b0c8
-- title:
--   OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound` of [lean/OAI/Geometry/EinsteinFour/Boundary.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/Boundary.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour.Boundary`, with `open Potential`):
--
--   ```lean
--   theorem zeroOrder_bound {v b σ τ : ℝ}
--       (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
--       (hσ : σ ≤ 1) (hτ : τ ≤ 1)
--       (hvdefect : v ^ 2 * (1 - σ) ≤ 2 * (2 - v - b) ^ 2)
--       (hbdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
--       zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.couplingCoefficient`, `OAI.PositiveEinsteinFour.Boundary.zeroOrderIntegrand` and `OAI.PositiveEinsteinFour.Potential.theta` (definitions bundle `OAIQ091C001` of this split).
--
--   **Used by.** The proof of `OAI.PositiveEinsteinFour.reduced_integrand_bound` of this split imports it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/Boundary.lean (declaration OAI.PositiveEinsteinFour.Boundary.zeroOrder_bound)

import Mathlib
import Definitions.Def_OAIQ091C001

section

attribute [-instance] _root_.OAI.PositiveEinsteinFour.Geometry.radialCubicMeasure_openPos
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PositiveEinsteinFour.Boundary

open Potential

noncomputable section

theorem zeroOrder_bound {v b σ τ : ℝ}
    (hv : 0 ≤ v) (hb : 0 ≤ b) (hsum : v + b ≤ 2)
    (hσ : σ ≤ 1) (hτ : τ ≤ 1)
    (hvdefect : v ^ 2 * (1 - σ) ≤ 2 * (2 - v - b) ^ 2)
    (hbdefect : b ^ 2 * (1 - τ) ≤ 2 * (2 - v - b) ^ 2) :
    zeroOrderIntegrand v b σ τ ≤ -theta v b ^ 2 / couplingCoefficient v b := by
  sorry

end

end PositiveEinsteinFour.Boundary

end OAI
end
