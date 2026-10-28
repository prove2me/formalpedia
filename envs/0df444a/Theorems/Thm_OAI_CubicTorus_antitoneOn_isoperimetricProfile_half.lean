-- Prove2me | Theorems.Thm_OAI_CubicTorus_antitoneOn_isoperimetricProfile_half
-- name    : OAI.CubicTorus.antitoneOn_isoperimetricProfile_half
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:52:25.779378+00:00
-- url     : https://prove2.me/theorems/09974bfb-8f5a-4e42-85b8-b11e3cd14183
-- title:
--   OAI.CubicTorus.antitoneOn_isoperimetricProfile_half: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.antitoneOn_isoperimetricProfile_half` of [lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem antitoneOn_isoperimetricProfile_half :
--       AntitoneOn isoperimetricProfile (Icc (1/2 : ℝ) 1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.isoperimetricProfile` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.Periodic.connected_CMC_strict_sign` and `OAI.CubicTorus.profile_upper_support_slope_nonpos` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Estimates/TubeCalibration.lean (declaration OAI.CubicTorus.antitoneOn_isoperimetricProfile_half)

import Mathlib
import Definitions.Def_OAIQ079A000

section

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

theorem antitoneOn_isoperimetricProfile_half :
    AntitoneOn isoperimetricProfile (Icc (1/2 : ℝ) 1) := by
  sorry

end CubicTorus

end
end

end

end OAI
end
