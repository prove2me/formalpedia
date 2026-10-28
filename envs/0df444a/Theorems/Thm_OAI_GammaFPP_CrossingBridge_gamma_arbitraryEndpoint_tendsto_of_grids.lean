-- Prove2me | Theorems.Thm_OAI_GammaFPP_CrossingBridge_gamma_arbitraryEndpoint_tendsto_of_grids
-- name    : OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T03:55:15.82879+00:00
-- url     : https://prove2.me/theorems/0ed7a59c-0fd3-467f-94c2-5a5e3b50bb1f
-- title:
--   OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.GammaFPP.gamma_differentiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids` of [lean/OAI/Probability/GammaPassage/EndpointLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/EndpointLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.GammaFPP.CrossingBridge`, with `open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem gamma_arbitraryEndpoint_tendsto_of_grids {ι : Type*} {l : Filter ι}
--       (henv : GammaEnvironment shape rate P τ)
--       (hshape : 0 < shape) (hrate : 0 < rate)
--       (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 100 ≤ K)
--       (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
--       (k m : ι → ℕ) (hk : Tendsto k l atTop)
--       (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
--       (hm : ∀ᶠ i in l, m i ≤ 3*k i)
--       (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
--         P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hshape hrate) (direction b)) K A R (k i) (m i) J} ≤
--           Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J) :
--       Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b ((gammaMeanNorm henv hshape hrate) (direction b))
--         (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε (k i) (m i)}) l (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.GammaFPP.gammaMeanNorm`, `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.extremeSlope`, `OAI.GammaFPP.CrossingBridge.arbitraryEndpointEvent`, `OAI.GammaFPP.CrossingBridge.gridConnectionsEvent`, `OAI.GammaFPP.CrossingBridge.gridIndexConstant` and `OAI.GammaFPP.Grid.gridFailureTail` (definitions bundle `OAIW2GF000` of this split); `OAI.GammaFPP.GammaEnvironment` and `OAI.PlanarFPP.Edge` (the published bundle `Def_GammaPassage`).
--
--   **Used by.** The proof of `OAI.GammaFPP.CrossingBridge.gamma_spatial_witness_BK_scales` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/GammaPassage/EndpointLimit.lean (declaration OAI.GammaFPP.CrossingBridge.gamma_arbitraryEndpoint_tendsto_of_grids)

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
open PlanarFPP GammaFPP.RealDirectionBridge Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {shape rate : ℝ}
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem gamma_arbitraryEndpoint_tendsto_of_grids {ι : Type*} {l : Filter ι}
    (henv : GammaEnvironment shape rate P τ)
    (hshape : 0 < shape) (hrate : 0 < rate)
    (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 100 ≤ K)
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
    (k m : ι → ℕ) (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i)
    (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent shape rate b ((gammaMeanNorm henv hshape hrate) (direction b)) K A R (k i) (m i) J} ≤
        Grid.gridFailureTail shape (gridIndexConstant A R) q₀ J) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b ((gammaMeanNorm henv hshape hrate) (direction b))
      (extremeSlope (gammaMeanNorm henv hshape hrate) b plus) A R ε (k i) (m i)}) l (𝓝 0) := by
  sorry

end GammaFPP.CrossingBridge

end OAI
end
