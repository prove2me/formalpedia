-- Prove2me | Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_goodSiteEvent_failure
-- name    : OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:55:08.394809+00:00
-- url     : https://prove2.me/theorems/90b0891f-9ab4-4997-a3d0-c5448f1c099b
-- title:
--   OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure` of [lean/OAI/Probability/GammaPassage/GoodSiteProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/GoodSiteProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.CrossingBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem gamma_goodSiteEvent_failure (h : GammaEnvironment shape rate P τ)
--       (hshape : 0 < shape) (hrate : 0 < rate)
--       (b A R ε : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
--       (hR : 0 ≤ R) (hε : 0 < ε) :
--       ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
--         ∀ (n : ℤ) (v : Vertex) (p0 : ℝ),
--         p0 ≤ P.real {ω | (fun e => τ e ω) ∈
--           rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} →
--         P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} <
--           (1-p0)^M+κ
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm`, `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.extremeSlope`, `OAI.GammaFPP.CrossingBridge.goodSiteEvent` and `OAI.GammaFPP.CrossingBridge.rareFastEvent` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment`, `OAI.PlanarFPP.Edge` and `OAI.PlanarFPP.Vertex` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proofs of `OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids` and `OAI.GammaFPP.CrossingBridge.gamma_characteristic_lengths_exist` of this split import it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/GoodSiteProbability.lean (declaration OAI.GammaFPP.CrossingBridge.gamma_goodSiteEvent_failure)

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
open PlanarFPP GammaFPP.RealDirectionBridge Set Finset MeasureTheory ProbabilityTheory Filter
open scoped Topology

variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gamma_goodSiteEvent_failure (h : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b A R ε : ℝ) (hb : |b| ≤ 1) (plus : Bool) (M : ℕ) (hM : 0 < M)
    (hR : 0 ≤ R) (hε : 0 < ε) :
    ∃ D0 : ℝ, 1 ≤ D0 ∧ ∀ κ > 0, ∀ᶠ s : ℝ in atTop,
      ∀ (n : ℤ) (v : Vertex) (p0 : ℝ),
      p0 ≤ P.real {ω | (fun e => τ e ω) ∈
        rareFastEvent b ((gammaMeanNorm h hshape hrate) (direction b)) (extremeSlope (gammaMeanNorm h hshape hrate) b plus) A R ε s n 0} →
      P.real {ω | (fun e => τ e ω) ∉ goodSiteEvent (gammaMeanNorm h hshape hrate) b A R ε s plus n ⌈D0*s⌉ M v} <
        (1-p0)^M+κ := by
  sorry

end GammaFPP.CrossingBridge

end OAI
end
