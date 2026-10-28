-- Prove2me | Theorems.Thm_OAI_CubicTorus_NestingGain_integrated_uniform_gain
-- name    : OAI.CubicTorus.NestingGain.integrated_uniform_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T15:46:06.046758+00:00
-- url     : https://prove2.me/theorems/acffeb9f-dce8-4b1b-ab8e-77dd570e038e
-- title:
--   OAI.CubicTorus.NestingGain.integrated_uniform_gain: intermediate lemma from OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicTorus.NestingGain.integrated_uniform_gain` of [lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicTorus.NestingGain`, with `open Set MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory`, `open scoped Interval`, `open CubicTorus.Nesting CubicTorus.Shape`):
--
--   ```lean
--   theorem integrated_uniform_gain {h δ : ℝ}
--       (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hδ : δ ∈ Icc 0 dm) :
--       min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) * δ ^ 3 ≤
--         δ * ∫ q in (0 : ℝ)..1,
--           (weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
--             weight (h * (u h - δ + δ * q)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicTorus.Nesting.weight`, `OAI.CubicTorus.Shape.c`, `OAI.CubicTorus.Shape.dm`, `OAI.CubicTorus.Shape.shape` and `OAI.CubicTorus.Shape.u` (definitions bundle `OAIQ079A000` of this split).
--
--   **Used by.** The proof of `OAI.CubicTorus.isMinimizerAt_nesting_cubic_gain` of this split imports it.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingEndpointBound.lean (declaration OAI.CubicTorus.NestingGain.integrated_uniform_gain)

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
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.NestingGain
open CubicTorus.Nesting CubicTorus.Shape

theorem integrated_uniform_gain {h δ : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hδ : δ ∈ Icc 0 dm) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) * δ ^ 3 ≤
      δ * ∫ q in (0 : ℝ)..1,
        (weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
          weight (h * (u h - δ + δ * q))) := by
  sorry

end CubicTorus.NestingGain

end
end
end

end

end OAI
end
