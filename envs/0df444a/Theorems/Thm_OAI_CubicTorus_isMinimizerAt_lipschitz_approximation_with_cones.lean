-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_lipschitz_approximation_with_cones
-- name    : OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:05:05.081996+00:00
-- url     : https://prove2.me/theorems/1aeb914c-f2af-46db-ab3a-074cbd717c6e
-- title:
--   OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones` of [lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_lipschitz_approximation_with_cones {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
--       ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 0 < C ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
--         ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
--         ∃ S : Set Torus, S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2) ∧
--           (spatialNormalMeasure μ : Measure Torus)
--             ((frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2)) \ S) ≤
--             ENNReal.ofReal C * ENNReal.ofReal
--               (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
--                 ∂(spatialNormalMeasure μ : Measure Torus)) ∧
--           (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ ρ →
--             |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c) ∧
--           ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
--             ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
--               ⟪n, shortestLift (x - a)⟫
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.normalPlaneProjection`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.shortestLift` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean (declaration OAI.CubicTorus.isMinimizerAt_lipschitz_approximation_with_cones)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.MovingCenter.instCoeInteriorCenterCover _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_lipschitz_approximation_with_cones {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2) :
    ∃ ρ₀ C : ℝ, 0 < ρ₀ ∧ 0 < C ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      ∃ S : Set Torus, S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2) ∧
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (ρ / 2)) \ S) ≤
          ENNReal.ofReal C * ENNReal.ofReal
            (∫ x in Metric.closedBall a (17 * ρ), ‖N x - n‖ ^ 2
              ∂(spatialNormalMeasure μ : Measure Torus)) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ ρ →
          |⟪n, shortestLift (x - c)⟫| ≤ ε * dist x c) ∧
        ∃ g : Cover → ℝ, LipschitzWith ⟨2 * ε, by positivity⟩ g ∧
          ∀ x ∈ S, g (normalPlaneProjection n (shortestLift (x - a))) =
            ⟪n, shortestLift (x - a)⟫ := by
  sorry

end CubicTorus

end
end

end

end OAI
end
