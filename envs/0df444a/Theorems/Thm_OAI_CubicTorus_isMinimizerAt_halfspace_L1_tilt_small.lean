-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_halfspace_L1_tilt_small
-- name    : OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:04:58.655158+00:00
-- url     : https://prove2.me/theorems/679d68c2-ad8a-46fb-8b69-a0e7b445512a
-- title:
--   OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small` of [lean/OAI/Geometry/CubicTorus/Variation/ComponentDivergence.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/ComponentDivergence.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_halfspace_L1_tilt_small {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
--       (hH : ∀ D : WallVariation, normalFirstVariation μ D =
--         H*directionalFlux E D.coordinate D.function)
--       {n : Cover} (hn : ‖n‖ = 1) {ε : ℝ} (hε : 0 < ε) :
--       ∃ η : ℝ, 0 < η ∧ ∀ (c : MovingCenter.InteriorCenter) (r : ℝ),
--         0 < r → r < η →
--         (∫ x in Metric.closedBall (0 : Cover) 1,
--           |blowupCharacteristic E c r x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
--         (∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c r 2 : Measure BlowupNormalBundle)) < ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.BlowupNormalBundle`, `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.blowupCharacteristic`, `OAI.CubicTorus.blowupNormalMeasure`, `OAI.CubicTorus.blowupTilt`, `OAI.CubicTorus.coverHalfspace`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.normalFirstVariation` and `OAI.CubicTorus.MovingCenter.InteriorCenter` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt` and `OAI.CubicTorus.Torus` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.actual_primary_fixed_scale_packets` and `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Variation/ComponentDivergence.lean (declaration OAI.CubicTorus.isMinimizerAt_halfspace_L1_tilt_small)

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
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_halfspace_L1_tilt_small {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) {H : ℝ}
    (hH : ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function)
    {n : Cover} (hn : ‖n‖ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (c : MovingCenter.InteriorCenter) (r : ℝ),
      0 < r → r < η →
      (∫ x in Metric.closedBall (0 : Cover) 1,
        |blowupCharacteristic E c r x-(coverHalfspace n).indicator (fun _ ↦ (1 : ℝ)) x|) < η →
      (∫ z, blowupTilt n z ∂(blowupNormalMeasure μ c r 2 : Measure BlowupNormalBundle)) < ε := by
  sorry

end CubicTorus

end
end

end

end OAI
end
