-- Prove2me | Theorems.Thm_OAI_GammaFPP_IntervalTravelBridge_gamma_moving_goodOrigin_failure_tendsto
-- name    : OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:56:40.551981+00:00
-- url     : https://prove2.me/theorems/e2b7870c-ec29-489d-b9af-47a77b97255e
-- title:
--   OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto` of [lean/OAI/Probability/GammaPassage/MovingOrigin.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/MovingOrigin.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.IntervalTravelBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set`, `open scoped Topology`):
--
--   ```lean
--   theorem gamma_moving_goodOrigin_failure_tendsto
--       (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
--       (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
--       (a : ℕ → Vertex) :
--       Tendsto (fun n => P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
--         (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a n) e) ω)})
--         atTop (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.cheapSlope`, `OAI.GammaFPP.gammaMeanNorm`, `OAI.PlanarFPP.shiftEdge` and `OAI.GammaFPP.IntervalTravelBridge.GoodOrigin` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proofs of `OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure` and `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/MovingOrigin.lean (declaration OAI.GammaFPP.IntervalTravelBridge.gamma_moving_goodOrigin_failure_tendsto)

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

namespace GammaFPP.IntervalTravelBridge
open PlanarFPP GammaFPP.RealDirectionBridge MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
variable {τ : Edge → Ω → ℝ} {ν : Measure ℝ} {shape rate : ℝ}

theorem gamma_moving_goodOrigin_failure_tendsto
    (h : GammaEnvironment shape rate P τ) (hs : 0 < shape) (hr : 0 < rate)
    (C : ℕ) (hC : 0 < C) (η δ : ℝ) (hη : 0 < η) (hδ : 0 < δ)
    (a : ℕ → Vertex) :
    Tendsto (fun n => P.real {ω | ¬GoodOrigin (gammaMeanNorm h hs hr)
      (cheapSlope shape rate) C η δ n (fun e => τ (shiftEdge (a n) e) ω)})
      atTop (𝓝 0) := by
  sorry

end GammaFPP.IntervalTravelBridge

end OAI
end
