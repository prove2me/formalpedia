-- Prove2me | Theorems.Thm_OAI_CubicTorus_isMinimizerAt_centered_multiplier
-- name    : OAI.CubicTorus.isMinimizerAt_centered_multiplier
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:01:33.074774+00:00
-- url     : https://prove2.me/theorems/6afe32ac-dc85-4ebe-9207-5c3c6c92c041
-- title:
--   OAI.CubicTorus.isMinimizerAt_centered_multiplier: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isMinimizerAt_centered_multiplier` of [lean/OAI/Geometry/CubicTorus/Estimates/BVInteriorMultiplier.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVInteriorMultiplier.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_centered_multiplier {V : ℝ} (hV : V ∈ Ioo 0 1)
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
--       {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
--       ∃ H : ℝ, ∀ D : WallVariation, normalFirstVariation μ D =
--         H*directionalFlux E D.coordinate D.function
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.CompactCell`, `OAI.CubicTorus.IsNormalMeasure`, `OAI.CubicTorus.NormalBundle`, `OAI.CubicTorus.NormalSphere`, `OAI.CubicTorus.WallVariation`, `OAI.CubicTorus.cubeCenter`, `OAI.CubicTorus.directionalFlux`, `OAI.CubicTorus.normalFirstVariation` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_lipschitz_graph`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_field`, `OAI.CubicTorus.MovingCenter.isMinimizerAt_moving_normal_modulus`, `OAI.CubicTorus.isMinimizerAt_centered_C1_modulus` and `OAI.CubicTorus.isMinimizerAt_centered_holder_CMC` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/BVInteriorMultiplier.lean (declaration OAI.CubicTorus.isMinimizerAt_centered_multiplier)

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
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem isMinimizerAt_centered_multiplier {V : ℝ} (hV : V ∈ Ioo 0 1)
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : quotientMap cubeCenter ∈ frontier (openRepresentative E))
    {μ : FiniteMeasure NormalBundle} (hμ : IsNormalMeasure E μ) :
    ∃ H : ℝ, ∀ D : WallVariation, normalFirstVariation μ D =
      H*directionalFlux E D.coordinate D.function := by
  sorry

end CubicTorus

end
end

end

end OAI
end
