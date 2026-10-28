-- Prove2me | Theorems.Thm_OAI_CubicTorus_actual_tangent_secondary_representation
-- name    : OAI.CubicTorus.actual_tangent_secondary_representation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:51:40.767304+00:00
-- url     : https://prove2.me/theorems/ff9a3d0d-20ab-4b51-8fe7-cd3ada07640c
-- title:
--   OAI.CubicTorus.actual_tangent_secondary_representation: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.actual_tangent_secondary_representation` of [lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem actual_tangent_secondary_representation {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
--       {A : Set Cover} (hA : MeasurableSet A)
--       (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
--         |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
--         atTop (𝓝 0))
--       (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
--       (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
--       ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
--         Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
--           |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
--           atTop (𝓝 0) ∧
--         ∃ (c : ℕ → Cover) (q : ℕ → ℝ), (∀ i, ‖c i-cubeCenter‖ ≤ 1/8) ∧
--           (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
--           Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
--             |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
--             atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.blowupCharacteristic` and `OAI.CubicTorus.cubeCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Reflection/BVConeSecondaryFlux.lean (declaration OAI.CubicTorus.actual_tangent_secondary_representation)

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

theorem actual_tangent_secondary_representation {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (r : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    {A : Set Cover} (hA : MeasurableSet A)
    (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 2,
      |blowupCharacteristic E cubeCenter (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
      atTop (𝓝 0))
    (p : Cover) (hp : ‖p‖ < 1) (s : ℕ → ℝ) (hs : ∀ i, 0 < s i)
    (hs1 : ∀ i, s i ≤ 1) (hslim : Tendsto s atTop (𝓝 0)) :
    ∃ B : Set Cover, MeasurableSet B ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
        |A.indicator (fun _ ↦ (1 : ℝ)) (p+s (φ i) • x)-B.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0) ∧
      ∃ (c : ℕ → Cover) (q : ℕ → ℝ), (∀ i, ‖c i-cubeCenter‖ ≤ 1/8) ∧
        (∀ i, 0 < q i) ∧ Tendsto q atTop (𝓝 0) ∧
        Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) 1,
          |blowupCharacteristic E (c i) (q i) x-B.indicator (fun _ ↦ (1 : ℝ)) x|)
          atTop (𝓝 0) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
