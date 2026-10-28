-- Prove2me | Theorems.Thm_OAI_CubicTorus_Periodic_isMinimizerAt_power_affine_spherical
-- name    : OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:48:29.736533+00:00
-- url     : https://prove2.me/theorems/09bfbea1-c108-40d4-ada1-d12e6e0fd37e
-- title:
--   OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical` of [lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.Periodic`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isMinimizerAt_power_affine_spherical {V : ℝ} (hV : V∈Ioo 0 (1/2))
--       {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
--       (hc : IsPreconnected (frontier (openRepresentative E))) {a b : ℝ}
--       (he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=a*W+b) :
--       ∃ (c : Cover) (r : ℝ),0 < r ∧ r<1/2 ∧
--         frontier (openRepresentative E)=quotientMap '' Metric.sphere c r
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.isoperimetricProfile` and `OAI.CubicTorus.openRepresentative` (definitions bundle `OAIQ079A000` of this split); `OAI.CubicTorus.Cover`, `OAI.CubicTorus.IsMinimizerAt`, `OAI.CubicTorus.Torus` and `OAI.CubicTorus.quotientMap` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proof of `OAI.CubicTorus.unit_cubic_isoperimetric` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/LocalGraphSphere.lean (declaration OAI.CubicTorus.Periodic.isMinimizerAt_power_affine_spherical)

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
namespace Periodic

theorem isMinimizerAt_power_affine_spherical {V : ℝ} (hV : V∈Ioo 0 (1/2))
    {E : Set Torus} (hE : MeasurableSet E) (hmin : IsMinimizerAt V E)
    (hc : IsPreconnected (frontier (openRepresentative E))) {a b : ℝ}
    (he : ∀ᶠ W in 𝓝 V,isoperimetricProfile W^(3/2 : ℝ)=a*W+b) :
    ∃ (c : Cover) (r : ℝ),0 < r ∧ r<1/2 ∧
      frontier (openRepresentative E)=quotientMap '' Metric.sphere c r := by
  sorry

end Periodic
end CubicTorus

end
end

end

end OAI
end
