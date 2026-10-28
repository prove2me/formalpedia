-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_centered_C1_modulus
-- name    : OAI.CubicTorus.isMinimizerAt_centered_C1_modulus
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:01:10.598269+00:00
-- url     : https://prove2.me/theorems/b92a151b-9839-49e2-b19e-6f7526754180
-- title:
--   OAI.CubicTorus.isMinimizerAt_centered_C1_modulus: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus` of [lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_centered_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
--       ∃ (n : Cover) (g : Plane → ℝ) (r M ρ : ℝ), ‖n‖=1 ∧ 0 < r ∧
--         0≤M ∧ 0<ρ ∧ ρ≤1/16 ∧
--         LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
--         (∀ y ∈ Metric.ball (0 : Plane) r,
--           quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
--         (∀ x∈Metric.ball (0 : Cover) r,
--           quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
--             normalGraph n g (normalPlaneCoordinates n x)=x) ∧
--         (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) r, ∀ y∈Metric.ball (0 : Plane) r,
--           dist x y≤ρ^i*r → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.Plane`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.normalPlaneCoordinates` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_centered_holder_CMC` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/TorusC2CMCAt.lean (declaration OAI.CubicTorus.isMinimizerAt_centered_C1_modulus)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ (n : Cover) (g : Plane → ℝ) (r M ρ : ℝ), ‖n‖=1 ∧ 0 < r ∧
      0≤M ∧ 0<ρ ∧ ρ≤1/16 ∧
      LipschitzWith (1/4) g ∧ g 0=0 ∧ ContDiffOn ℝ 1 g (Metric.ball 0 r) ∧
      (∀ y ∈ Metric.ball (0 : Plane) r,
        quotientMap (cubeCenter+normalGraph n g y)∈frontier (openRepresentative E)) ∧
      (∀ x∈Metric.ball (0 : Cover) r,
        quotientMap (cubeCenter+x)∈frontier (openRepresentative E) ↔
          normalGraph n g (normalPlaneCoordinates n x)=x) ∧
      (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) r, ∀ y∈Metric.ball (0 : Plane) r,
        dist x y≤ρ^i*r → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
