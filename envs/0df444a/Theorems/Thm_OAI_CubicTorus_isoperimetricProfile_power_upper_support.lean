-- Prove2me | Theorems.Thm_OAI_CubicTorus_isoperimetricProfile_power_upper_support
-- name    : OAI.CubicTorus.isoperimetricProfile_power_upper_support
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:16:41.374517+00:00
-- url     : https://prove2.me/theorems/a8c4596a-792b-4ae3-8bb1-a9c7d227c203
-- title:
--   OAI.CubicTorus.isoperimetricProfile_power_upper_support: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.isoperimetricProfile_power_upper_support` of [lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem isoperimetricProfile_power_upper_support {V : ℝ} (hV : V∈Ioo 0 1) :
--       ∃ D : ℝ → ℝ,Reduction.UpperSupport (fun W ↦ isoperimetricProfile W^(3/2 : ℝ)) D V ∧
--         deriv (deriv D) V≤0
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.isoperimetricProfile` and `OAI.CubicTorus.Reduction.UpperSupport` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.profile_upper_support_power_secant` and `OAI.CubicTorus.unit_cubic_isoperimetric` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean (declaration OAI.CubicTorus.isoperimetricProfile_power_upper_support)

import Mathlib
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

theorem isoperimetricProfile_power_upper_support {V : ℝ} (hV : V∈Ioo 0 1) :
    ∃ D : ℝ → ℝ,Reduction.UpperSupport (fun W ↦ isoperimetricProfile W^(3/2 : ℝ)) D V ∧
      deriv (deriv D) V≤0 := by
  sorry

end CubicTorus

end
end

end

end OAI
end
