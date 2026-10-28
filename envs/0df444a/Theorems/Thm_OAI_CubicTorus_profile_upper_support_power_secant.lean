-- Prove2me | Theorems.Thm_OAI_CubicTorus_profile_upper_support_power_secant
-- name    : OAI.CubicTorus.profile_upper_support_power_secant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:22:01.429142+00:00
-- url     : https://prove2.me/theorems/119bf679-f7e9-4a81-825d-d6331170b4ac
-- title:
--   OAI.CubicTorus.profile_upper_support_power_secant: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.profile_upper_support_power_secant` of [lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem profile_upper_support_power_secant {a V : ℝ} (ha : 0≤a) (hV : V∈Ioo 0 1)
--       (haV : a<V) {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
--       (3/2 : ℝ)*deriv C V*Real.sqrt (isoperimetricProfile V) ≤
--         (isoperimetricProfile V^(3/2 : ℝ)-isoperimetricProfile a^(3/2 : ℝ))/(V-a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.isoperimetricProfile` and `OAI.CubicTorus.Reduction.UpperSupport` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_second_endpoint_linear_bound` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/FourStarScalarGrid.lean (declaration OAI.CubicTorus.profile_upper_support_power_secant)

import Mathlib
import Definitions.Def_OAIQ079A000

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

theorem profile_upper_support_power_secant {a V : ℝ} (ha : 0≤a) (hV : V∈Ioo 0 1)
    (haV : a<V) {C : ℝ → ℝ} (hs : Reduction.UpperSupport isoperimetricProfile C V) :
    (3/2 : ℝ)*deriv C V*Real.sqrt (isoperimetricProfile V) ≤
      (isoperimetricProfile V^(3/2 : ℝ)-isoperimetricProfile a^(3/2 : ℝ))/(V-a) := by
  sorry

end CubicTorus

end
end

end OAI
end
