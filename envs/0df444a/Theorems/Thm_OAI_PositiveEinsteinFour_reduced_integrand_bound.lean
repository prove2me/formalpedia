-- Prove2me | Theorems.Thm_OAI_PositiveEinsteinFour_reduced_integrand_bound
-- name    : OAI.PositiveEinsteinFour.reduced_integrand_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T17:11:57.298336+00:00
-- url     : https://prove2.me/theorems/59606cea-138c-4fcb-8cff-af191279bf0d
-- title:
--   OAI.PositiveEinsteinFour.reduced_integrand_bound: intermediate lemma from OpenAI, Positively curved Einstein four-manifolds (result family 348)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PositiveEinsteinFour.classification`, `OAI.PositiveEinsteinFour.classificationOn` and `OAI.PositiveEinsteinFour.orientedClassification`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Positively curved Einstein four-manifolds (result family 348)*, OpenAI Math Release, September 23, 2026, result family 348, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PositiveEinsteinFour.reduced_integrand_bound` of [lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PositiveEinsteinFour`, with `open Energy QuarticEnergy QuarticClosed Quadratic Boundary Potential`):
--
--   ```lean
--   theorem reduced_integrand_bound
--       {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
--       {v b r s σ τ ρ χ e f : ℝ} (p q : E)
--       (hv : 0 ≤ v) (hb : 0 ≤ b)
--       (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
--       (hspectral : v * r + b * s ≤ 2)
--       (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
--       (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
--       (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) (hf : (5 / 3) * ‖q‖ ^ 2 ≤ f)
--       (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
--       reducedIntegrand v b r s σ τ ρ χ e f p q ≤
--         -couplingCoefficient v b * (‖p‖ ^ 2 + ‖q‖ ^ 2) *
--           (‖p‖ ^ 2 / v + ‖q‖ ^ 2 / b) +
--         2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) -
--         theta v b ^ 2 / couplingCoefficient v b
--   ```
--
--   **Definitions.** The statement is written with `OAI.PositiveEinsteinFour.couplingCoefficient` and `OAI.PositiveEinsteinFour.Potential.theta` (definitions bundle `OAIQ091C001` of this split); `OAI.PositiveEinsteinFour.normWeight` (definitions bundle `OAIQ091C004` of this split); `OAI.PositiveEinsteinFour.reducedIntegrand` (definitions bundle `OAIQ091C012` of this split).
--
--   **Used by.** The proofs of `OAI.PositiveEinsteinFour.Geometry.MetricGreenData.one_block_zero_of_variance` and `OAI_PositiveEinsteinFour_QuaternionFrame_pointwise_coupling_bound_closed` of this split import it.
-- source:
--   OpenAI, Positively curved Einstein four-manifolds (result family 348), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 348; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Positively-curved-Einstein-four-manifolds-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/EinsteinFour/WeylEstimates00.lean (declaration OAI.PositiveEinsteinFour.reduced_integrand_bound)

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

theorem reduced_integrand_bound
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {v b r s σ τ ρ χ e f : ℝ} (p q : E)
    (hv : 0 ≤ v) (hb : 0 ≤ b)
    (hr : 1 ≤ r) (hr2 : r ≤ 2) (hs : 1 ≤ s) (hs2 : s ≤ 2)
    (hspectral : v * r + b * s ≤ 2)
    (hσ : σ = (3 * r - r ^ 3) / 2) (hρ : ρ ^ 2 = 1 - σ ^ 2)
    (hτ : τ = (3 * s - s ^ 3) / 2) (hχ : χ ^ 2 = 1 - τ ^ 2)
    (he : (5 / 3) * ‖p‖ ^ 2 ≤ e) (hf : (5 / 3) * ‖q‖ ^ 2 ≤ f)
    (hve : v = 0 → e = 0) (hbf : b = 0 → f = 0) :
    reducedIntegrand v b r s σ τ ρ χ e f p q ≤
      -couplingCoefficient v b * (‖p‖ ^ 2 + ‖q‖ ^ 2) *
        (‖p‖ ^ 2 / v + ‖q‖ ^ 2 / b) +
      2 * theta v b * (normWeight v * ‖p‖ ^ 2 + normWeight b * ‖q‖ ^ 2) -
      theta v b ^ 2 / couplingCoefficient v b := by
  sorry

end
end PositiveEinsteinFour
end

end OAI
end
