-- Prove2me | Theorems.Thm_OAI_CubicTorus_SmallStandardRegion_bv_data
-- name    : OAI.CubicTorus.SmallStandardRegion.bv_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:35:58.668996+00:00
-- url     : https://prove2.me/theorems/ac8b79a8-c8c3-45f9-a392-52c0076e34d3
-- title:
--   OAI.CubicTorus.SmallStandardRegion.bv_data: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.SmallStandardRegion.bv_data` of [lean/OAI/Geometry/CubicTorus/Rigidity/TwoVolumeNodal.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/TwoVolumeNodal.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem SmallStandardRegion.bv_data {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ))
--       {E : Set Torus} (hE : SmallStandardRegion V E) :
--       FinitePerimeter E ∧ torusVolume E=ENNReal.ofReal V ∧
--         perimeter E=ENNReal.ofReal (candidateProfile V)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.FinitePerimeter`, `OAI.CubicTorus.SmallStandardRegion`, `OAI.CubicTorus.Torus`, `OAI.CubicTorus.candidateProfile`, `OAI.CubicTorus.perimeter` and `OAI.CubicTorus.torusVolume` (the published bundle `Def_CubicTorus`).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_second_endpoint_linear_bound`, `OAI.CubicTorus.isoperimetricProfile_cylinder_interval`, `OAI.CubicTorus.isoperimetricProfile_second_transition` and `OAI.CubicTorus.unit_cubic_isoperimetric` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Rigidity/TwoVolumeNodal.lean (declaration OAI.CubicTorus.SmallStandardRegion.bv_data)

import Mathlib
import Definitions.Def_CubicTorus

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem SmallStandardRegion.bv_data {V : ℝ} (hV : V∈Ioc 0 (1/2 : ℝ))
    {E : Set Torus} (hE : SmallStandardRegion V E) :
    FinitePerimeter E ∧ torusVolume E=ENNReal.ofReal V ∧
      perimeter E=ENNReal.ofReal (candidateProfile V) := by
  sorry

end CubicTorus

end
end

end OAI
end
