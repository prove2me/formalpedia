-- Prove2me | Theorems.Thm_OAI_CubicTorus_MovingCenter_weakCMC_normalized_sequence_harmonic
-- name    : OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:45:12.026554+00:00
-- url     : https://prove2.me/theorems/4e925257-98a8-4c03-a29a-829af22ef380
-- title:
--   OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic` of [lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.MovingCenter`, with `open MeasureTheory Set Filter Metric`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`, `open Laplacian`):
--
--   ```lean
--   theorem weakCMC_normalized_sequence_harmonic {U : Set Torus} (hU : IsOpen U)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
--       (hH : ∀ D : WallVariation, normalFirstVariation μ D =
--         H*directionalFlux U D.coordinate D.function)
--       {N : Torus → Cover} (hN : Measurable N)
--       (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
--       (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
--       (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e m C : ℕ → ℝ) (g : ℕ → Plane → ℝ) (A : ℝ)
--       (hn : ∀ i, ‖n i‖ = 1) (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < 3/8)
--       (hα : ∀ i, α i < 1/4) (he : ∀ i, 0 < e i)
--       (htrap : ∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure U)ᶜ ∧
--         normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ U)
--       (htilt : ∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
--         ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2)
--       (ha : ∀ i, (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c i : Cover)) (r i)) ≤ A*(r i)^2)
--       (hg : ∀ i, Continuous (g i))
--       (hcol : ∀ i, (∫ y in Metric.ball (0 : Plane) (r i/4),
--         |g i y-normalColumnHeight U (quotientMap (c i : Cover)) (n i) (r i) y|) ≤ C i*(r i)^3*(e i)^2)
--       (helim : Tendsto e atTop (𝓝 0)) (hClim : Tendsto C atTop (𝓝 0))
--       (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0)) :
--       ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
--         tsupport φ ⊆ Metric.ball (0 : Plane) (1/4) →
--         Tendsto (fun i ↦ ∫ y, graphNormalize (r i) (e i) (m i) (g i) y*Δ φ y) atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.graphNormalize`, `OAI.CubicTorus.normalCap`, `OAI.CubicTorus.normalColumnHeight`, `OAI.CubicTorus.normalFirstVariation`, `OAI.CubicTorus.spatialNormalMeasure` and `OAI.CubicTorus.MovingCenter.InteriorCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.MovingCenter.isMinimizerAt_trapped_sequential_decay` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVMovingOrientedReplacement.lean (declaration OAI.CubicTorus.MovingCenter.weakCMC_normalized_sequence_harmonic)

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
open Laplacian
namespace CubicTorus.MovingCenter
variable {c : InteriorCenter}

theorem weakCMC_normalized_sequence_harmonic {U : Set Torus} (hU : IsOpen U)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure U μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux U D.coordinate D.function)
    {N : Torus → Cover} (hN : Measurable N)
    (hp : ∀ᵐ z ∂(μ : Measure NormalBundle), N (quotientMap z.1) = (z.2 : Cover))
    (hu : ∀ᵐ x ∂(spatialNormalMeasure μ : Measure Torus), ‖N x‖ = 1)
    (c : ℕ → InteriorCenter) (n : ℕ → Cover) (r α e m C : ℕ → ℝ) (g : ℕ → Plane → ℝ) (A : ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < 3/8)
    (hα : ∀ i, α i < 1/4) (he : ∀ i, 0 < e i)
    (htrap : ∀ i, normalCap (quotientMap (c i : Cover)) (n i) (r i) (α i*r i) ⊆ (closure U)ᶜ ∧
      normalCap (quotientMap (c i : Cover)) (-(n i)) (r i) (α i*r i) ⊆ U)
    (htilt : ∀ i, (∫ x in Metric.closedBall (quotientMap (c i : Cover)) (17*r i), ‖N x-n i‖^2
      ∂(spatialNormalMeasure μ : Measure Torus)) ≤ (r i)^2*(e i)^2)
    (ha : ∀ i, (spatialNormalMeasure μ : Measure Torus).real (Metric.ball (quotientMap (c i : Cover)) (r i)) ≤ A*(r i)^2)
    (hg : ∀ i, Continuous (g i))
    (hcol : ∀ i, (∫ y in Metric.ball (0 : Plane) (r i/4),
      |g i y-normalColumnHeight U (quotientMap (c i : Cover)) (n i) (r i) y|) ≤ C i*(r i)^3*(e i)^2)
    (helim : Tendsto e atTop (𝓝 0)) (hClim : Tendsto C atTop (𝓝 0))
    (hrel : Tendsto (fun i ↦ r i/(e i)^2) atTop (𝓝 0)) :
    ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball (0 : Plane) (1/4) →
      Tendsto (fun i ↦ ∫ y, graphNormalize (r i) (e i) (m i) (g i) y*Δ φ y) atTop (𝓝 0) := by
  sorry

end CubicTorus.MovingCenter

end
end

end

end OAI
end
