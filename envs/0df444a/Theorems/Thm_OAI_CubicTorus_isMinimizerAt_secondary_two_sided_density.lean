-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_secondary_two_sided_density
-- name    : OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:10:37.119257+00:00
-- url     : https://prove2.me/theorems/f1ea7791-34dd-4445-806d-61177e84fdc0
-- title:
--   OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density` of [lean/OAI/Geometry/CubicTorus/Regularity/BVPlanarEssentialBoundary.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVPlanarEssentialBoundary.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_secondary_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
--       ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
--         ∀ A : Set Cover, MeasurableSet A →
--         Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
--           |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
--         ∀ p : Cover, ‖p‖ < 1 →
--         (∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
--           0 < volume.real (Aᶜ ∩ Metric.ball p δ)) →
--         ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) →
--         ∀ B : Set Cover, MeasurableSet B →
--         Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
--           |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
--         ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
--           b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
--           b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.blowupCharacteristic` and `OAI.CubicTorus.cubeCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVPlanarEssentialBoundary.lean (declaration OAI.CubicTorus.isMinimizerAt_secondary_two_sided_density)

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

theorem isMinimizerAt_secondary_two_sided_density {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E) :
    ∃ b : ℝ, 0 < b ∧ ∀ r : ℕ → ℝ, (∀ i, 0 < r i) → Tendsto r atTop (𝓝 0) →
      ∀ A : Set Cover, MeasurableSet A →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
        |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ p : Cover, ‖p‖ < 1 →
      (∀ δ : ℝ, 0 < δ → 0 < volume.real (A ∩ Metric.ball p δ) ∧
        0 < volume.real (Aᶜ ∩ Metric.ball p δ)) →
      ∀ s : ℕ → ℝ, (∀ i, 0 < s i) → Tendsto s atTop (𝓝 0) →
      ∀ B : Set Cover, MeasurableSet B →
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s i • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|) atTop (𝓝 0) →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        b*ρ^3 ≤ volume.real (B ∩ Metric.ball (0 : Cover) ρ) ∧
        b*ρ^3 ≤ volume.real (Bᶜ ∩ Metric.ball (0 : Cover) ρ) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
