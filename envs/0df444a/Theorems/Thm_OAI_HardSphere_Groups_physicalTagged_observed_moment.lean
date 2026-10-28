-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physicalTagged_observed_moment
-- name    : OAI.HardSphere.Groups.physicalTagged_observed_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:57:51.396898+00:00
-- url     : https://prove2.me/theorems/62acf7f4-f10f-4dfd-b6d3-03a8e2fb9e1a
-- title:
--   OAI.HardSphere.Groups.physicalTagged_observed_moment: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal BigOperators`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice`):
--
--   ```lean
--   theorem physicalTagged_observed_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
--       (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
--       (particle : J↪Fin (N+1)) (hxy : x≠y)
--       (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
--       (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
--       (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
--       (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
--       (hBt : routeDensityBound t≤ENNReal.ofReal B)
--       (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
--       (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
--       (hdata : ∀ᵐd ∂μ.restrict E,
--         (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
--         (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
--         (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
--         (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
--           physicalCollisionReference hL g m t r R C S u particle d j
--             {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
--       (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
--       (b : Bool) {Y : Type*} [MeasurableSpace Y]
--       (obs : Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))) Y)
--       [IsMarkovKernel obs] :
--       Integrable (fun z ↦ ((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
--         (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2)
--         (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) ∧
--       (∫z,((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
--         (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2
--         ∂((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd)≤B*Cpath
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.TrialCollision`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectCurve`, `OAI.HardSphere.Comparison.departureSites`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.branchAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.datumIndividualReference`, `OAI.HardSphere.Groups.physicalCollisionReference`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Groups.routeDensityBound`, `OAI.HardSphere.Lattice.DiscreteTorus`, `OAI.HardSphere.Lattice.SimplePath`, `OAI.HardSphere.Lattice.simpleEncounter`, `OAI.HardSphere.Lattice.simplePathMeasurableSpace`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.physicalTaggedMixture` and `OAI.HardSphere.Groups.physicalTaggedReference` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_common_observed_estimates` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

theorem physicalTagged_observed_moment {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [IsFiniteMeasure μ]
    (E : Set (PhysicalDatum (N+1) K M G L)) (hE : MeasurableSet E)
    (hM : 0<M) (q : ℝ≥0∞) (δ B κ Cpath : ℝ) (hδ : 0<δ) (hB : 1≤B) (hCpath : 0≤Cpath)
    (hBt : routeDensityBound t≤ENNReal.ofReal B)
    (hκ : 2*(B-1)/(M:ℝ)-8*Real.log δ≤κ)
    (hsmall : ENNReal.ofReal δ+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀v∈departureSites p,(M:ℝ)≤2*((branchAccessible hL g m t r R C S u particle v d).card:ℝ)) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q))
    (henc : (∫⁻d in E,∫⁻p,∫⁻p',ENNReal.ofReal (Real.exp (κ*(simpleEncounter 30 p p':ℝ))) ∂ν d ∂ν d ∂μ)≤ENNReal.ofReal Cpath)
    (b : Bool) {Y : Type*} [MeasurableSpace Y]
    (obs : Kernel (Fin (N+1)×(PhysicalDatum (N+1) K M G L×(Option J→C(Time,Point)))) Y)
    [IsMarkovKernel obs] :
    Integrable (fun z ↦ ((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2)
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) ∧
    (∫z,((((physicalTaggedMixture hL g m t r R C S u particle hxy b ν μ E).compProd obs).map Prod.snd).rnDeriv
      (((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd) z).toReal^2
      ∂((physicalTaggedReference (x:=x) (y:=y) hL g m t r R C S u particle b μ).compProd obs).map Prod.snd)≤B*Cpath := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
