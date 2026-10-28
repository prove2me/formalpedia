-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_tightly_trapped_graph_approximation
-- name    : OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:13:21.701982+00:00
-- url     : https://prove2.me/theorems/5e9c8318-f362-4fed-a1f0-8ecd847cda7c
-- title:
--   OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation` of [lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_tightly_trapped_graph_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
--       ∃ r₀ : ℝ, ∃ C : ℝ≥0∞, 0 < r₀ ∧ C < ⊤ ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
--         ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ r α : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1 / 4 →
--           (normalCap a n r (α * r) ⊆ (closure (openRepresentative E))ᶜ ∧
--             normalCap a (-n) r (α * r) ⊆ openRepresentative E) →
--         ∃ (S : Set Torus) (g : Plane → ℝ),
--           LipschitzWith ⟨2 * η, by positivity⟩ g ∧
--           (∀ y, |g y| ≤ α * r) ∧
--           S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (r / 2) ∧
--           (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
--             ⟪n, shortestLift (x - a)⟫) ∧
--           (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ r →
--             |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) ∧
--           let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
--             ∂(spatialNormalMeasure μ : Measure Torus))
--           (spatialNormalMeasure μ : Measure Torus)
--             ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ C * e ∧
--           (∫⁻ y in Metric.ball (0 : Plane) (r / 4), ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2)) ≤ C * e ∧
--           (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
--             ENNReal.ofReal (columnGraphMismatch (openRepresentative E) a n r g y)) ≤
--               C * ENNReal.ofReal α * ENNReal.ofReal r * e
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.columnGraphMismatch`, `OAI.CubicTorus.normalCap`, `OAI.CubicTorus.normalPlaneCoordinates`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.shortestLift` and `OAI.CubicTorus.spatialNormalMeasure` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/BVColumnMismatchMeasure.lean (declaration OAI.CubicTorus.isMinimizerAt_tightly_trapped_graph_approximation)

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

theorem isMinimizerAt_tightly_trapped_graph_approximation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {η : ℝ} (hη : 0 < η) (hηhalf : η ≤ 1 / 2) :
    ∃ r₀ : ℝ, ∃ C : ℝ≥0∞, 0 < r₀ ∧ C < ⊤ ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (a : Torus) (n : Cover), ‖n‖ = 1 → ∀ r α : ℝ, 0 < r → r ≤ r₀ → 0 ≤ α → α < 1 / 4 →
        (normalCap a n r (α * r) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap a (-n) r (α * r) ⊆ openRepresentative E) →
      ∃ (S : Set Torus) (g : Plane → ℝ),
        LipschitzWith ⟨2 * η, by positivity⟩ g ∧
        (∀ y, |g y| ≤ α * r) ∧
        S ⊆ frontier (openRepresentative E) ∩ Metric.ball a (r / 2) ∧
        (∀ x ∈ S, g (normalPlaneCoordinates n (shortestLift (x - a))) =
          ⟪n, shortestLift (x - a)⟫) ∧
        (∀ c ∈ S, ∀ x ∈ frontier (openRepresentative E), dist x c ≤ r →
          |⟪n, shortestLift (x - c)⟫| ≤ η * dist x c) ∧
        let e := ENNReal.ofReal (∫ x in Metric.closedBall a (17 * r), ‖N x - n‖ ^ 2
          ∂(spatialNormalMeasure μ : Measure Torus))
        (spatialNormalMeasure μ : Measure Torus)
          ((frontier (openRepresentative E) ∩ Metric.ball a (r / 2)) \ S) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4), ENNReal.ofReal (‖fderiv ℝ g y‖ ^ 2)) ≤ C * e ∧
        (∫⁻ y in Metric.ball (0 : Plane) (r / 4),
          ENNReal.ofReal (columnGraphMismatch (openRepresentative E) a n r g y)) ≤
            C * ENNReal.ofReal α * ENNReal.ofReal r * e := by
  sorry

end CubicTorus

end
end

end

end OAI
end
