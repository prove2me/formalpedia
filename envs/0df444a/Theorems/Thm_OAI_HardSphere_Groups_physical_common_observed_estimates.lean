-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physical_common_observed_estimates
-- name    : OAI.HardSphere.Groups.physical_common_observed_estimates
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:54:50.633227+00:00
-- url     : https://prove2.me/theorems/b9208a35-5f88-4d46-ba97-dbffe03265ca
-- title:
--   OAI.HardSphere.Groups.physical_common_observed_estimates: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal BigOperators`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice`):
--
--   ```lean
--   theorem physical_common_observed_estimates {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
--       (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
--       (particle : J↪Fin (N+1)) (hxy : x≠y)
--       (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
--       (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
--       (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
--       (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
--       (hBt : routeDensityBound t≤ENNReal.ofReal B)
--       (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
--       (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
--       (hdata : ∀ᵐd ∂μ.restrict E,PhysicalMomentData hL g m t r R C S u particle ν q d)
--       (hprimary : ∀ᵐd ∂μ.restrict E,IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
--       (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath) :
--       let σ := physicalCommonObserved hL g m t r R C S u particle hxy ν μ E
--       σ univ=μ E ∧ ∀b,
--         let P := physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ
--         σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
--           (∫z,(σ.rnDeriv P z).toReal^2 ∂P)≤B*Cpath
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.PhysicalMomentData`, `OAI.HardSphere.Groups.routeDensityBound`, `OAI.HardSphere.Groups.siteIndex`, `OAI.HardSphere.Lattice.DiscreteTorus`, `OAI.HardSphere.Lattice.SimplePath`, `OAI.HardSphere.Lattice.simpleEncounter`, `OAI.HardSphere.Lattice.simplePathMeasurableSpace`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.physicalCommonObserved`, `OAI.HardSphere.Groups.physicalObservedReference` and `OAI.HardSphere.Groups.physicalPrimaryReference` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_group_common_comparison` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physical_common_observed_estimates {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,PhysicalMomentData hL g m t r R C S u particle ν q d)
    (hprimary : ∀ᵐd ∂μ.restrict E,IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath) :
    let σ := physicalCommonObserved hL g m t r R C S u particle hxy ν μ E
    σ univ=μ E ∧ ∀b,
      let P := physicalObservedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ
      σ≪P ∧ Integrable (fun z ↦ (σ.rnDeriv P z).toReal^2) P ∧
        (∫z,(σ.rnDeriv P z).toReal^2 ∂P)≤B*Cpath := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
