-- Prove2me | Theorems.Thm_OAI_CubicTorus_moving_blowup_perimeter_eq_normal_ball
-- name    : OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:18:35.779488+00:00
-- url     : https://prove2.me/theorems/57860189-7604-4337-b6cd-1cbff2a967b5
-- title:
--   OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball` of [lean/OAI/Geometry/CubicTorus/Estimates/BVPlanarLocalModels.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVPlanarLocalModels.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem moving_blowup_perimeter_eq_normal_ball {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
--       (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
--       {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
--       {A : Set Cover} (hA : MeasurableSet A)
--       (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
--         |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
--       {ν : FiniteMeasure BlowupNormalBundle}
--       (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
--       (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
--         tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
--         (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
--       {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
--       coverLocalPerimeter A (Metric.ball (0 : Cover) b) =
--         (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) b}
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.blowupCharacteristic`, `OAI.CubicTorus.blowupNormalMeasure`, `OAI.CubicTorus.coverLocalPerimeter`, `OAI.CubicTorus.cubeCenter` and `OAI.CubicTorus.MovingCenter.InteriorCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.divergence` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs` and `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVPlanarLocalModels.lean (declaration OAI.CubicTorus.moving_blowup_perimeter_eq_normal_ball)

import Mathlib
import Definitions.Def_CubicTorus
import Definitions.Def_OAIQ079A000

section

attribute [-instance] _root_.OAI.CubicTorus.axialVolumeHeight_finite _root_.OAI.CubicTorus.latticeAddAction _root_.OAI.CubicTorus.latticeMeasurableVAdd _root_.OAI.CubicTorus.latticeVolumeInvariant
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

theorem moving_blowup_perimeter_eq_normal_ball {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    {l : Filter ℕ} [NeBot l] (hrlim : Tendsto r l (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) l (𝓝 0))
    {ν : FiniteMeasure BlowupNormalBundle}
    (hν : Tendsto (fun i ↦ blowupNormalMeasure μ (c i) (r i) 2) l (𝓝 ν))
    (hflux : ∀ F : Cover → Cover, ContDiff ℝ (⊤ : ℕ∞) F →
      tsupport F ⊆ Metric.closedBall (0 : Cover) 1 →
      (∫ z, ⟪(z.2 : Cover),F z.1⟫ ∂(ν : Measure BlowupNormalBundle)) = ∫ x in A, divergence F x)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) :
    coverLocalPerimeter A (Metric.ball (0 : Cover) b) =
      (ν : Measure BlowupNormalBundle) {z | z.1 ∈ Metric.ball (0 : Cover) b} := by
  sorry

end CubicTorus

end
end

end

end OAI
end
