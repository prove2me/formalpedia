-- Prove2me | Theorems.Thm_OAI_CubicTorus_actual_primary_offvertex_C1
-- name    : OAI.CubicTorus.actual_primary_offvertex_C1
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:51:33.813576+00:00
-- url     : https://prove2.me/theorems/2f2a6c72-979e-43d4-a16e-000cd2939854
-- title:
--   OAI.CubicTorus.actual_primary_offvertex_C1: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.actual_primary_offvertex_C1` of [lean/OAI/Geometry/CubicTorus/Regularity/CoverEssentialBoundary.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/CoverEssentialBoundary.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`):
--
--   ```lean
--   theorem actual_primary_offvertex_C1 {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hH : ∀ D : WallVariation, normalFirstVariation μ D =
--         H*directionalFlux E D.coordinate D.function)
--       (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
--       {A : Set Cover} (hA : MeasurableSet A)
--       (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
--         |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|)
--         atTop (𝓝 0))
--       (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
--         (t⁻¹ • x ∈ A ↔ x ∈ A))
--       {σ : FiniteMeasure BlowupNormalBundle}
--       (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
--         tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
--         (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
--         (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
--       (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
--       (hboundary : p ∈ coverEssentialBoundary A) : CoverC1BoundaryAt A p
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.CoverC1BoundaryAt`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.blowupCharacteristic`, `OAI.CubicTorus.coverEssentialBoundary`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.normalFirstVariation`, `OAI.CubicTorus.openRepresentative` and `OAI.CubicTorus.tangentialDivergence` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.divergence` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_strict_C1_cone_blowup` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/CoverEssentialBoundary.lean (declaration OAI.CubicTorus.actual_primary_offvertex_C1)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem actual_primary_offvertex_C1 {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hcenter : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1:ℝ)) x|)
      atTop (𝓝 0))
    (hcone : ∀ t : ℝ, 1 ≤ t → ∀ᵐ x ∂(volume : Measure Cover), x ∈ Metric.ball (0 : Cover) 1 →
      (t⁻¹ • x ∈ A ↔ x ∈ A))
    {σ : FiniteMeasure BlowupNormalBundle}
    (hstationary : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, tangentialDivergence F z.1 z.2 ∂(σ : Measure BlowupNormalBundle)) = 0 ∧
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(σ : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    (p : Cover) (hp : ‖p‖ < 1) (hp0 : p ≠ 0)
    (hboundary : p ∈ coverEssentialBoundary A) : CoverC1BoundaryAt A p := by
  sorry

end CubicTorus
end
end
end

end OAI
end
