-- Prove2me | Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_trapped_sequential_decay
-- name    : OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:46:12.057849+00:00
-- url     : https://prove2.me/theorems/74d9baa8-06f6-48c7-bd77-b13a885c1f4a
-- title:
--   OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay` of [lean/OAI/Geometry/CubicTorus/Estimates/BVMovingTrappedDecay.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVMovingTrappedDecay.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.MovingCenter`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`):
--
--   ```lean
--   theorem isMinimizerAt_trapped_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
--         ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
--           (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
--         ∀ N : Torus → Cover, Measurable N →
--           (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
--           (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
--         ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
--           (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
--           (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
--           Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
--           Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
--           (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
--             normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
--           (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
--             ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
--         ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
--         ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
--           (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
--             (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
--             (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.graphSlopeNormal`, `OAI.CubicTorus.normalCap`, `OAI.CubicTorus.normalFirstVariation`, `OAI.CubicTorus.openRepresentative`, `OAI.CubicTorus.spatialNormalMeasure`, `OAI.CubicTorus.MovingCenter.InteriorCenter` and `OAI.CubicTorus.MovingCenter.bundleOrientedExcess` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field` and `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVMovingTrappedDecay.lean (declaration OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.finiteMeasure_cover_closedBall _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter Metric
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem isMinimizerAt_trapped_sequential_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ r₀ R K : ℝ, 0 < r₀ ∧ 0 < R ∧ R ≤ 1/8 ∧ 0 ≤ K ∧
      ∀ μ : FiniteMeasure NormalBundle, IsNormalMeasure E μ → ∀ H : ℝ,
        (∀ w : WallVariation, normalFirstVariation μ w = H*directionalFlux E w.coordinate w.function) →
      ∀ N : Torus → Cover, Measurable N →
        (∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover)) →
        (∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1) →
      ∀ (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e : ℕ → ℝ), (∀ i, ‖n i‖ = 1) →
        (∀ i, 0 < r i) → (∀ i, r i ≤ r₀) → (∀ i, 0 ≤ α i) → (∀ i, α i < 1/4) →
        (∀ i, 0 < e i) → (∀ i, e i ≤ 1/2) →
        Tendsto α atTop (𝓝 0) → Tendsto e atTop (𝓝 0) →
        Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0) →
        (∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure (openRepresentative E))ᶜ ∧
          normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ openRepresentative E) →
        (∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
          ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2) →
      ∀ θ ε : ℝ, 0 < θ → 2*θ ≤ R → 0 < ε →
      ∃ (ψ : ℕ → ℕ) (p : Plane →L[ℝ] ℝ), StrictMono ψ ∧ ∀ᶠ i in atTop,
        (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
          (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
          (r (ψ i))^2*(e (ψ i))^2*(K*θ^4+ε) := by
  sorry

end CubicTorus.MovingCenter

end
end

end

end OAI
end
