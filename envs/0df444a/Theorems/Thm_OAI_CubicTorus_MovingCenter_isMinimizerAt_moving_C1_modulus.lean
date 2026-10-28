-- Prove2me | Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_moving_C1_modulus
-- name    : OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:41:18.742051+00:00
-- url     : https://prove2.me/theorems/6059f4de-fa8e-4d6f-8d99-cddd56cf9976
-- title:
--   OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus` of [lean/OAI/Geometry/CubicTorus/Curvature/LinearCMCEquationNear.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/LinearCMCEquationNear.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.MovingCenter`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_moving_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
--       ∃ r₀ ρ : ℝ, 0 < r₀ ∧ 0<ρ ∧ ρ≤1/16 ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1)=(z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖=1) →
--         ∃ δ : ℝ, 0<δ ∧ ∀ c₀ : Cover, ‖c₀-cubeCenter‖≤1/16 →
--           quotientMap c₀∈frontier (openRepresentative E) → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖=1 →
--           0 < r → r ≤ r₀ → 0<e → e≤δ → r/e^2≤δ →
--           (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
--             ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
--         ∃ (g : Plane → ℝ) (M : ℝ), 0≤M ∧ LipschitzWith (1/4) g ∧
--           ContDiffOn ℝ 1 g (Metric.ball 0 (r/1024)) ∧
--           (∀ y∈Metric.ball (0 : Plane) (r/1024),
--             quotientMap c₀+quotientMap (normalGraph n₀ g y)∈frontier (openRepresentative E) ∧
--             ‖normalGraph n₀ g y‖ < r/512) ∧
--           (∀ x∈quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
--             normalGraph n₀ g (normalPlaneCoordinates n₀ (x-c₀))=x-c₀) ∧
--           (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) (r/1024), ∀ y∈Metric.ball (0 : Plane) (r/1024),
--             dist x y≤ρ^i*(r/4) → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.normalGraph`, `OAI.CubicTorus.normalPlaneCoordinates`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Curvature/LinearCMCEquationNear.lean (declaration OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_C1_modulus)

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
namespace CubicTorus.MovingCenter

theorem isMinimizerAt_moving_C1_modulus {V : ℝ} (hV : V∈Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter∈frontier (openRepresentative E)) :
    ∃ r₀ ρ : ℝ, 0 < r₀ ∧ 0<ρ ∧ ρ≤1/16 ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1)=(z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖=1) →
      ∃ δ : ℝ, 0<δ ∧ ∀ c₀ : Cover, ‖c₀-cubeCenter‖≤1/16 →
        quotientMap c₀∈frontier (openRepresentative E) → ∀ (n₀ : Cover) (r e : ℝ), ‖n₀‖=1 →
        0 < r → r ≤ r₀ → 0<e → e≤δ → r/e^2≤δ →
        (∫ x in Metric.closedBall (quotientMap c₀) (17*r), ‖N x-n₀‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ r^2*e^2 →
      ∃ (g : Plane → ℝ) (M : ℝ), 0≤M ∧ LipschitzWith (1/4) g ∧
        ContDiffOn ℝ 1 g (Metric.ball 0 (r/1024)) ∧
        (∀ y∈Metric.ball (0 : Plane) (r/1024),
          quotientMap c₀+quotientMap (normalGraph n₀ g y)∈frontier (openRepresentative E) ∧
          ‖normalGraph n₀ g y‖ < r/512) ∧
        (∀ x∈quotientMap ⁻¹' frontier (openRepresentative E) ∩ Metric.ball c₀ (r/128),
          normalGraph n₀ g (normalPlaneCoordinates n₀ (x-c₀))=x-c₀) ∧
        (∀ i : ℕ, ∀ x∈Metric.ball (0 : Plane) (r/1024), ∀ y∈Metric.ball (0 : Plane) (r/1024),
          dist x y≤ρ^i*(r/4) → dist (fderiv ℝ g x) (fderiv ℝ g y)≤M*(1/2:ℝ)^i) := by
  sorry

end CubicTorus.MovingCenter

end
end

end

end OAI
end
