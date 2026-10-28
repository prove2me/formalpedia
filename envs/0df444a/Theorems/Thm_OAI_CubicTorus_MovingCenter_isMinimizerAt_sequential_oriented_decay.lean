-- Prove2me | Theorems.Thm_OAI_CubicTorus_MovingCenter_isMinimizerAt_sequential_oriented_decay
-- name    : OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:25:48.879427+00:00
-- url     : https://prove2.me/theorems/0b307a69-5aba-4d97-8e12-61d231d32c77
-- title:
--   OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay` of [lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.MovingCenter`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`):
--
--   ```lean
--   theorem isMinimizerAt_sequential_oriented_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       (c : ℕ → InteriorCenter) (r e m h B : ℕ → ℝ) (n : ℕ → Cover) (f : ℕ → Plane → ℝ)
--       (hr : ∀ i, 0 < r i) (he : ∀ i, 0 < e i) (hn : ∀ i, ‖n i‖ = 1)
--       (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
--       (hrlim : Tendsto r atTop (𝓝 0)) (helim : Tendsto e atTop (𝓝 0))
--       (hmlim : Tendsto m atTop (𝓝 0)) (hhlim : Tendsto h atTop (𝓝 0))
--       (hBlim : Tendsto B atTop (𝓝 0))
--       (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0))
--       {θ : ℝ} (hθ : 0 < θ) {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
--       (p : Plane →L[ℝ] ℝ) {A H : ℝ} (hA : 0 ≤ A)
--       (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
--       (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
--       (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
--       (hheight : ∀ i y, ‖y‖ < 2*θ → |m i+e i*f i y| ≤ h i)
--       (hmismatch : ∀ i,
--         sublevelVolume (E ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
--           (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i)
--       {ε : ℝ} (hε : 0 < ε) :
--       ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
--         (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
--           (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
--         (r (ψ i))^2*(e (ψ i))^2*(2*H+ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.graphRescale`, `OAI.CubicTorus.graphSlopeNormal`, `OAI.CubicTorus.MovingCenter.InteriorCenter`, `OAI.CubicTorus.MovingCenter.bundleOrientedExcess` and `OAI.CubicTorus.MovingCenter.radialSquared` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.sublevelVolume` and `OAI.CubicTorus.torusGraphRegion` (definitions bundle `OAIQ079A003` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean (declaration OAI.CubicTorus.MovingCenter.isMinimizerAt_sequential_oriented_decay)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A003

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

theorem isMinimizerAt_sequential_oriented_decay {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → InteriorCenter) (r e m h B : ℕ → ℝ) (n : ℕ → Cover) (f : ℕ → Plane → ℝ)
    (hr : ∀ i, 0 < r i) (he : ∀ i, 0 < e i) (hn : ∀ i, ‖n i‖ = 1)
    (hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hrlim : Tendsto r atTop (𝓝 0)) (helim : Tendsto e atTop (𝓝 0))
    (hmlim : Tendsto m atTop (𝓝 0)) (hhlim : Tendsto h atTop (𝓝 0))
    (hBlim : Tendsto B atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0))
    {θ : ℝ} (hθ : 0 < θ) {u : Plane → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (p : Plane →L[ℝ] ℝ) {A H : ℝ} (hA : 0 ≤ A)
    (henergy : ∀ i, (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ (f i) y-p‖^2) ≤ A)
    (hH : (∫ y in Metric.ball (0 : Plane) (2*θ), ‖fderiv ℝ u y-p‖^2) ≤ H)
    (hconv : Tendsto (fun i ↦ ∫ y in Metric.ball (0 : Plane) (2*θ), (f i y-u y)^2) atTop (𝓝 0))
    (hheight : ∀ i y, ‖y‖ < 2*θ → |m i+e i*f i y| ≤ h i)
    (hmismatch : ∀ i,
      sublevelVolume (E ∆ torusGraphRegion (c i : Cover) (n i) (graphRescale (r i) (e i) (m i) (f i)))
        (radialSquared (c i)) ((r i*(2*θ))^2) < (r i)^3*(e i)^2*B i)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∀ᶠ i in atTop,
      (bundleOrientedExcess (c (ψ i))) μ (graphSlopeNormal (n (ψ i))
        (e (ψ i) • (InnerProductSpace.toDual ℝ Plane).symm p)) (r (ψ i)*θ) ≤
      (r (ψ i))^2*(e (ψ i))^2*(2*H+ε) := by
  sorry

end CubicTorus.MovingCenter

end
end

end

end OAI
end
