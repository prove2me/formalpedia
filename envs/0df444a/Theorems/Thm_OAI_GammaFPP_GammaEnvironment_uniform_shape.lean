-- Prove2me | Theorems.Thm_OAI_GammaFPP_GammaEnvironment_uniform_shape
-- name    : OAI.GammaFPP.GammaEnvironment.uniform_shape
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:20.202519+00:00
-- url     : https://prove2.me/theorems/6562b8ca-2dd8-42f9-98e5-f53f9b007649
-- title:
--   OAI.GammaFPP.GammaEnvironment.uniform_shape: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.GammaEnvironment.uniform_shape` of [lean/OAI/Probability/GammaPassage/UniformShape.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/UniformShape.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP`, with `open MeasureTheory ProbabilityTheory PlanarFPP Real Filter Set`, `open GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge`, `open scoped Topology`):
--
--   ```lean
--   theorem GammaEnvironment.uniform_shape
--       (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
--       ∀ᵐ ω ∂P, UniformShapeBridge.UniformShape (fun e => τ e ω) (gammaMeanNorm h hs hr)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm` and `OAI.GammaFPP.UniformShapeBridge.UniformShape` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment` and `OAI.PlanarFPP.Edge` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proofs of `OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids`, `OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist` and `OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/UniformShape.lean (declaration OAI.GammaFPP.GammaEnvironment.uniform_shape)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_GammaPassage
import Definitions.Def_OAIW2GF000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace GammaFPP
open MeasureTheory ProbabilityTheory PlanarFPP Real Filter Set
open GammaFPP.RealDirectionBridge GammaFPP.UniformShapeBridge
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.uniform_shape
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate) :
    ∀ᵐ ω ∂P, UniformShapeBridge.UniformShape (fun e => τ e ω) (gammaMeanNorm h hs hr) := by
  sorry

end GammaFPP

end OAI
end
