-- Prove2me | Theorems.Thm_OAI_PlanarFPP_actual_differentiable_horizontal
-- name    : OAI.PlanarFPP.actual_differentiable_horizontal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:10.162368+00:00
-- url     : https://prove2.me/theorems/a744d84a-01d7-4e00-bdab-b65c270dcaef
-- title:
--   OAI.PlanarFPP.actual_differentiable_horizontal: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.actual_differentiable_horizontal` of [lean/OAI/Probability/FirstPassage/GlobalDifferentiability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GlobalDifferentiability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open MeasureTheory`):
--
--   ```lean
--   lemma actual_differentiable_horizontal (henv : ExponentialEnvironment P τ)
--       (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
--       DifferentiableAt ℝ actualSourceTimeConstant v
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.actualSourceTimeConstant` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment` and `OAI.PlanarFPP.Plane` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.manuscriptMain` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/GlobalDifferentiability.lean (declaration OAI.PlanarFPP.actual_differentiable_horizontal)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma actual_differentiable_horizontal (henv : ExponentialEnvironment P τ)
    (v : Plane) (hv : v ≠ 0) (hdom : |v 1| ≤ |v 0|) :
    DifferentiableAt ℝ actualSourceTimeConstant v := by
  sorry

end PlanarFPP

end OAI
end
