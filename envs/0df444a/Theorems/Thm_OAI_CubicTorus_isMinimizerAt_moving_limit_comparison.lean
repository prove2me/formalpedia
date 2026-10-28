-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_moving_limit_comparison
-- name    : OAI.CubicTorus.isMinimizerAt_moving_limit_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:06:06.304025+00:00
-- url     : https://prove2.me/theorems/4edbaca5-35d9-4c96-96ff-c369ee113759
-- title:
--   OAI.CubicTorus.isMinimizerAt_moving_limit_comparison: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_moving_limit_comparison` of [lean/OAI/Geometry/CubicTorus/Regularity/BVStationaryDensity.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVStationaryDensity.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff`):
--
--   ```lean
--   theorem isMinimizerAt_moving_limit_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
--       (hrlim : Tendsto r atTop (𝓝 0))
--       {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
--       {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
--         |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
--           atTop (𝓝 0))
--       {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hbR : b ≤ R)
--       (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
--       coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
--         coverLocalPerimeter B (Metric.closedBall (0 : Cover) b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.blowupCharacteristic`, `OAI.CubicTorus.coverLocalPerimeter`, `OAI.CubicTorus.cubeCenter` and `OAI.CubicTorus.MovingCenter.InteriorCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.actual_primary_offvertex_fixed_graphs` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Regularity/BVStationaryDensity.lean (declaration OAI.CubicTorus.isMinimizerAt_moving_limit_comparison)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace symmDiff
namespace CubicTorus

theorem isMinimizerAt_moving_limit_comparison {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (c : ℕ → MovingCenter.InteriorCenter) (r : ℕ → ℝ) (hr : ∀ i, 0 < r i)
    (hrlim : Tendsto r atTop (𝓝 0))
    {A B : Set Cover} (hA : MeasurableSet A) (hB : MeasurableSet B)
    {R : ℝ} (hconv : Tendsto (fun i ↦ ∫ x in Metric.closedBall (0 : Cover) R,
      |blowupCharacteristic E (c i) (r i) x-A.indicator (fun _ ↦ (1 : ℝ)) x|)
        atTop (𝓝 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb1 : b ≤ 1) (hbR : b ≤ R)
    (hAB : A ∆ B ⊆ Metric.ball (0 : Cover) a) :
    coverLocalPerimeter A (Metric.ball (0 : Cover) b) ≤
      coverLocalPerimeter B (Metric.closedBall (0 : Cover) b) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
