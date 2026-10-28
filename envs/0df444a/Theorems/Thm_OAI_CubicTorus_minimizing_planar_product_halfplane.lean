-- Prove2me | Theorems.Thm_OAI_CubicTorus_minimizing_planar_product_halfplane
-- name    : OAI.CubicTorus.minimizing_planar_product_halfplane
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:17:37.525241+00:00
-- url     : https://prove2.me/theorems/14b9ee55-5dac-4bb2-8e71-386a40a51a87
-- title:
--   OAI.CubicTorus.minimizing_planar_product_halfplane: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.minimizing_planar_product_halfplane` of [lean/OAI/Geometry/CubicTorus/Estimates/BVSecondaryPlanarData.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVSecondaryPlanarData.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`):
--
--   ```lean
--   theorem minimizing_planar_product_halfplane
--       {B : Set Cover} {C : Set Plane} {n : Cover}
--       (hB : MeasurableSet B) (hC : MeasurableSet C) (hn : ‖n‖ = 1)
--       (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
--         B ∆ D ⊆ Metric.ball (0 : Cover) a →
--         coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
--           coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
--       (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
--         (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
--       (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
--         y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
--       {K : ℝ} (hK : 0 ≤ K)
--       (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
--         tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
--         ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
--       {ν : FiniteMeasure BlowupNormalBundle}
--       (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
--         (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
--       (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
--         tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
--         (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
--           ∫ x in B, divergence F x)
--       {b : ℝ} (hb : 0 < b)
--       (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
--         b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
--         b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)) :
--       ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
--         y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪m,y⟫)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.Plane`, `OAI.CubicTorus.coverLocalPerimeter` and `OAI.CubicTorus.normalColumnChart` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover` and `OAI.CubicTorus.divergence` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVSecondaryPlanarData.lean (declaration OAI.CubicTorus.minimizing_planar_product_halfplane)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

theorem minimizing_planar_product_halfplane
    {B : Set Cover} {C : Set Plane} {n : Cover}
    (hB : MeasurableSet B) (hC : MeasurableSet C) (hn : ‖n‖ = 1)
    (hmin : ∀ D : Set Cover, MeasurableSet D → ∀ a b : ℝ, 0 < a → a < b → b ≤ 1 →
      B ∆ D ⊆ Metric.ball (0 : Cover) a →
      coverLocalPerimeter B (Metric.ball (0 : Cover) b) ≤
        coverLocalPerimeter D (Metric.closedBall (0 : Cover) b))
    (hprod : ∀ᵐ z : ℝ × Plane ∂volume, |z.1| < 1/16 → ‖z.2‖ < 1/16 →
      (normalColumnChart 0 n z ∈ B ↔ z.2 ∈ C))
    (hc : ∀ t : ℝ, 1 ≤ t → ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (t⁻¹ • y ∈ C ↔ y ∈ C))
    {K : ℝ} (hK : 0 ≤ K)
    (hbv : ∀ φ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      tsupport φ ⊆ Metric.closedBall (0 : Plane) (1/32) → (∀ y, |φ y| ≤ 1) →
      ∀ u : Plane, ‖u‖ = 1 → |∫ y in C, fderiv ℝ φ y u| ≤ K)
    {ν : FiniteMeasure BlowupNormalBundle}
    (heq : ∀ r : ℝ, 0 < r → r ≤ 1 → coverLocalPerimeter B (Metric.ball (0 : Cover) r) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) r})
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) =
        ∫ x in B, divergence F x)
    {b : ℝ} (hb : 0 < b)
    (hden : ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
      b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)) :
    ∃ m : Plane, m ≠ 0 ∧ ∀ᵐ y : Plane ∂volume,
      y ∈ Metric.ball (0 : Plane) (1/16) → (y ∈ C ↔ 0 < ⟪m,y⟫) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
