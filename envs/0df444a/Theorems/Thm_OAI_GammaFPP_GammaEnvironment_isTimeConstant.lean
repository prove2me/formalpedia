-- Prove2me | Theorems.Thm_OAI_GammaFPP_GammaEnvironment_isTimeConstant
-- name    : OAI.GammaFPP.GammaEnvironment.isTimeConstant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:15.803209+00:00
-- url     : https://prove2.me/theorems/826fb32b-0db9-41d2-8133-e8b3b5e44234
-- title:
--   OAI.GammaFPP.GammaEnvironment.isTimeConstant: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.GammaEnvironment.isTimeConstant` of [lean/OAI/Probability/GammaPassage/ActualTimeConstant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/ActualTimeConstant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP`, with `open MeasureTheory PlanarFPP`):
--
--   ```lean
--   theorem GammaEnvironment.isTimeConstant
--       (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
--       IsTimeConstant P τ (gammaMeanNorm h hs hr)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge` and `OAI.PlanarFPP.IsTimeConstant` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proofs of `OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit`, `OAI.GammaFPP.GammaEnvironment.uniform_shape`, `OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto` and `OAI.GammaFPP.gamma_differentiability` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/ActualTimeConstant.lean (declaration OAI.GammaFPP.GammaEnvironment.isTimeConstant)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000

section

attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory PlanarFPP

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.isTimeConstant
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    IsTimeConstant P τ (gammaMeanNorm h hs hr) := by
  sorry

end GammaFPP

end OAI
end
