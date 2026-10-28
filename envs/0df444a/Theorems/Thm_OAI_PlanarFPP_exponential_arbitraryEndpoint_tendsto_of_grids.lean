-- Prove2me | Theorems.Thm_OAI_PlanarFPP_exponential_arbitraryEndpoint_tendsto_of_grids
-- name    : OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T10:41:14.292918+00:00
-- url     : https://prove2.me/theorems/533023b2-7446-4e6f-a9ad-9cfc5cdc60a7
-- title:
--   OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids: intermediate lemma from OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PlanarFPP.manuscriptMain`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Strict convexity and differentiability of the planar exponential first-passage limit shape*, OpenAI Math Release, September 24, 2026, result family 212, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids` of [lean/OAI/Probability/FirstPassage/EndpointLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/EndpointLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PlanarFPP`, with `open Set Filter MeasureTheory ProbabilityTheory`, `open scoped Topology`):
--
--   ```lean
--   theorem exponential_arbitraryEndpoint_tendsto_of_grids {ι : Type*} {l : Filter ι}
--       (henv : ExponentialEnvironment P τ)
--       (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
--       (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
--       (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
--       (k m : ι → ℕ) (hk : Tendsto k l atTop)
--       (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
--       (hm : ∀ᶠ i in l, m i ≤ 3*k i)
--       (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
--         P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} ≤
--           gridFailureTail (gridIndexConstant A R) q₀ J) :
--       Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
--         (extremeSlope μ b plus) A R ε (k i) (m i)}) l (𝓝 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PlanarFPP.direction`, `OAI.PlanarFPP.extremeSlope`, `OAI.PlanarFPP.gridFailureTail` and `OAI.PlanarFPP.gridIndexConstant` (definitions bundle `OAISPf001` of this split); `OAI.PlanarFPP.arbitraryEndpointEvent` and `OAI.PlanarFPP.gridConnectionsEvent` (definitions bundle `OAISPf002` of this split); `OAI.PlanarFPP.Edge`, `OAI.PlanarFPP.ExponentialEnvironment`, `OAI.PlanarFPP.IsTimeConstant`, `OAI.PlanarFPP.Plane` and `OAI.PlanarFPP.TimeConstantNorm` (the published bundle `Def_PlanarFirstPassage`).
--
--   **Used by.** The proof of `OAI.PlanarFPP.actual_spatial_rare_scales` of this split imports it.
-- source:
--   OpenAI, Strict convexity and differentiability of the planar exponential first-passage limit shape, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 212; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-convexity-and-differentiability-of-the-planar-exponential-first-passage-limit-shape-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FirstPassage/EndpointLimit.lean (declaration OAI.PlanarFPP.exponential_arbitraryEndpoint_tendsto_of_grids)

import Mathlib
import Definitions.Def_PlanarFirstPassage
import Definitions.Def_OAISPf002

section

attribute [-instance] _root_.OAI.CompanionFPP.expOneProbability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFPP
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {τ : Edge → Ω → ℝ}

theorem exponential_arbitraryEndpoint_tendsto_of_grids {ι : Type*} {l : Filter ι}
    (henv : ExponentialEnvironment P τ)
    (μ : Plane → ℝ) (hμ : TimeConstantNorm μ) (ht : IsTimeConstant P τ μ)
    (b K A R ε q₀ : ℝ) (hb : |b| ≤ 1) (hK : 0 ≤ K)
    (hA : 0 < A) (hR : 0 < R) (hε : 0 < ε) (hq : 0 < q₀) (plus : Bool)
    (k m : ι → ℕ) (hk : Tendsto k l atTop)
    (hratio : Tendsto (fun i => (2 : ℝ)^(m i)/(2 : ℝ)^(k i)) l atTop)
    (hm : ∀ᶠ i in l, m i ≤ 3*k i)
    (hgrid : ∀ J : ℕ, 1 ≤ J → ∀ᶠ i in l,
      P.real {ω | (fun e => τ e ω) ∉ gridConnectionsEvent b (μ (direction b)) K A R (k i) (m i) J} ≤
        gridFailureTail (gridIndexConstant A R) q₀ J) :
    Tendsto (fun i => P.real {ω | (fun e => τ e ω) ∈ arbitraryEndpointEvent b (μ (direction b))
      (extremeSlope μ b plus) A R ε (k i) (m i)}) l (𝓝 0) := by
  sorry

end PlanarFPP

end OAI
end
