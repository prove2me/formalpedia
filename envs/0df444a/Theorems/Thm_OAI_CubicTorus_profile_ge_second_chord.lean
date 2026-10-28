-- Prove2me | Theorems.Thm_OAI_CubicTorus_profile_ge_second_chord
-- name    : OAI.CubicTorus.profile_ge_second_chord
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T16:21:37.488932+00:00
-- url     : https://prove2.me/theorems/96aed753-5204-43d2-8015-f02ffe6ad77c
-- title:
--   OAI.CubicTorus.profile_ge_second_chord: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.profile_ge_second_chord` of [lean/OAI/Geometry/CubicTorus/Main.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Main.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus`, with `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology RealInnerProductSpace`):
--
--   ```lean
--   lemma profile_ge_second_chord {V : ℝ} (hV : V∈Icc (0 : ℝ) (1/Real.pi)) :
--       Real.pi*V ≤ isoperimetricProfile V
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.isoperimetricProfile` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proofs of `OAI.CubicTorus.isMinimizerAt_cylinder_contact_corner_excluded` and `OAI.CubicTorus.isMinimizerAt_cylinder_contact_not_three_vertices` of this split import it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Main.lean (declaration OAI.CubicTorus.profile_ge_second_chord)

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

lemma profile_ge_second_chord {V : ℝ} (hV : V∈Icc (0 : ℝ) (1/Real.pi)) :
    Real.pi*V ≤ isoperimetricProfile V := by
  sorry

end CubicTorus

end
end

end OAI
end
