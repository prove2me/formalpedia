-- Prove2me | Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_direction_nat_limit
-- name    : OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:55:12.504969+00:00
-- url     : https://prove2.me/theorems/88fb9cb9-fe63-42ed-a330-69e7faa072b8
-- title:
--   OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit` of [lean/OAI/Probability/GammaPassage/ActualNoCorner.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/ActualNoCorner.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.CrossingBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK`, `open MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma gamma_direction_nat_limit (henv : GammaEnvironment shape rate P τ)
--       (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) :
--       ∀ᵐ ω ∂P, Tendsto
--         (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
--         atTop (𝓝 ((gammaMeanNorm henv hshape hrate) (direction b)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm` and `OAI.PlanarFPP.direction` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.Vertex` and `OAI.PlanarFPP.passageTime` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proof of `OAI.GammaFPP.gamma_differentiability` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/ActualNoCorner.lean (declaration OAI.GammaFPP.CrossingBridge.gamma_direction_nat_limit)

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

namespace GammaFPP.CrossingBridge
open PlanarFPP GammaFPP.RealDirectionBridge GammaFPP.BK
open MeasureTheory Filter
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

lemma gamma_direction_nat_limit (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate) (b : ℝ) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => passageTime (fun e => τ e ω) 0 ((n : ℤ),⌊b*(n : ℝ)⌋)/(n : ℝ))
      atTop (𝓝 ((gammaMeanNorm henv hshape hrate) (direction b))) := by
  sorry

end GammaFPP.CrossingBridge

end OAI
end
