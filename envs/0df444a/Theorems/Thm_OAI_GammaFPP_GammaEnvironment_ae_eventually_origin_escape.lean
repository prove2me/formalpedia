-- Prove2me | Theorems.Thm_OAI_GammaFPP_GammaEnvironment_ae_eventually_origin_escape
-- name    : OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:19.887985+00:00
-- url     : https://prove2.me/theorems/e16c546d-0898-4629-b722-bb5102357095
-- title:
--   OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape` of [lean/OAI/Probability/GammaPassage/OriginEscapeLower.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/OriginEscapeLower.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP`, with `open PlanarFPP MeasureTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem GammaEnvironment.ae_eventually_origin_escape
--       (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
--       (δ : ℝ) (hδ : 0 < δ) :
--       ∀ᵐ ω ∂P, ∀ᶠ s : ℝ in atTop, ∀ z : Vertex,
--         δ*s/3 ≤ ‖RealDirectionBridge.latticeEmbed z‖ →
--         cheapSlope shape rate*δ*s/6 ≤ passageTime (fun e => τ e ω) 0 z
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.cheapSlope` and `OAI.GammaFPP.RealDirectionBridge.latticeEmbed` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.Plane`, `OAI.PlanarFPP.Vertex` and `OAI.PlanarFPP.passageTime` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proof of `OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/OriginEscapeLower.lean (declaration OAI.GammaFPP.GammaEnvironment.ae_eventually_origin_escape)

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
open PlanarFPP MeasureTheory Filter
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {shape rate : ℝ}

theorem GammaEnvironment.ae_eventually_origin_escape
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, ∀ᶠ s : ℝ in atTop, ∀ z : Vertex,
      δ*s/3 ≤ ‖RealDirectionBridge.latticeEmbed z‖ →
      cheapSlope shape rate*δ*s/6 ≤ passageTime (fun e => τ e ω) 0 z := by
  sorry

end GammaFPP

end OAI
end
