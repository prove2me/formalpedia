-- Prove2me | Theorems.Thm_OAI_PlanarFPP_actualSourceTimeConstant_lattice_limits
-- name    : OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:40:29.591992+00:00
-- url     : https://prove2.me/theorems/d2a2c46c-191e-4255-bc73-307e36ebf5b4
-- title:
--   OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits` of [lean/OAI/Probability/FirstPassage/ActualTimeConstant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/ActualTimeConstant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem actualSourceTimeConstant_lattice_limits (h : ExponentialEnvironment P τ) :
--       ∀ᵐ ω ∂P, ∀ z : Vertex,
--         Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z)/n) atTop
--           (𝓝 (actualSourceTimeConstant (latticeEmbed z)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.latticeEmbed` (definitions bundle `OAISPf000` of this split); `OAI.PlanarFPP.actualSourceTimeConstant` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.Vertex` and `OAI.PlanarFPP.passageTime` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proofs of `OAI.PlanarFPP.actual_differentiable_horizontal`, `OAI.PlanarFPP.actual_spatial_rare_scales` and `OAI.PlanarFPP.manuscriptMain` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/ActualTimeConstant.lean (declaration OAI.PlanarFPP.actualSourceTimeConstant_lattice_limits)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

attribute [-instance] _root_.OAI.PlanarFPP.instDecidableIsBoundarySide _root_.OAI.PlanarFPP.instDecidableLatticeNear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem actualSourceTimeConstant_lattice_limits (h : ExponentialEnvironment P τ) :
    ∀ᵐ ω ∂P, ∀ z : Vertex,
      Tendsto (fun n : ℕ => passageTime (fun e => τ e ω) 0 (n • z)/n) atTop
        (𝓝 (actualSourceTimeConstant (latticeEmbed z))) := by
  sorry

end PlanarFPP

end OAI
end
