-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physicalObservedMixture_mass
-- name    : OAI.HardSphere.Groups.physicalObservedMixture_mass
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:54:05.860369+00:00
-- url     : https://prove2.me/theorems/6209c71c-2c08-4cd4-8a3d-241c584dfa85
-- title:
--   OAI.HardSphere.Groups.physicalObservedMixture_mass: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice`):
--
--   ```lean
--   theorem physicalObservedMixture_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
--       (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
--       (particle : J↪Fin (N+1)) (hxy : x≠y)
--       (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
--       (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ] (E : Set (PhysicalDatum (N+1) K M G L))
--       (q a : ℝ≥0∞) (ha0 : 0<a)
--       (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
--       (hdata : ∀ᵐd ∂μ.restrict E,
--         (∀ᵐp ∂ν d,∀i : Fin p.val.length,
--           (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
--         (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
--         (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
--         (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
--           physicalCollisionReference hL g m t r R C S u particle d j
--             {p | TrialCollision r (projectCurve L f.val) p.val}≤q) ∧
--         IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
--       (b : Bool) :
--       ((μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν b)) univ=μ E
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.TrialCollision`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectCurve`, `OAI.HardSphere.Comparison.pathVertexEmbedding`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.branchAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.datumIndividualReference`, `OAI.HardSphere.Groups.physicalCollisionReference`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Groups.routeDensityBound`, `OAI.HardSphere.Groups.siteIndex`, `OAI.HardSphere.Lattice.DiscreteTorus`, `OAI.HardSphere.Lattice.SimplePath`, `OAI.HardSphere.Lattice.simplePathMeasurableSpace`, `OAI.HardSphere.Lattice.torusNearestGraph`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.physicalObservedMixture` and `OAI.HardSphere.Groups.physicalPrimaryReference` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_common_observed_estimates` of this split imports it.
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
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital _root_.OAI.HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {K : ℕ} [NeZero K] {x y : DiscreteTorus K}
variable {J : Type*} [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]

omit [MeasurableSpace J] [MeasurableSingletonClass J] in
theorem physicalObservedMixture_mass {N M G : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
    (particle : J↪Fin (N+1)) (hxy : x≠y)
    (ν : Kernel (PhysicalDatum (N+1) K M G L) (SimplePath x y)) [IsMarkovKernel ν]
    (μ : Measure (PhysicalDatum (N+1) K M G L)) [SFinite μ] (E : Set (PhysicalDatum (N+1) K M G L))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1)
    (hdata : ∀ᵐd ∂μ.restrict E,
      (∀ᵐp ∂ν d,∀i : Fin p.val.length,
        (branchAccessible hL g m t r R C S u particle (pathVertexEmbedding p i.castSucc) d).Nonempty) ∧
      (∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M) ∧
      (∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) ∧
      (∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u particle d (some k),
        physicalCollisionReference hL g m t r R C S u particle d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤q) ∧
      IsProbabilityMeasure (physicalPrimaryReference hL g m t r R C S u particle (siteIndex y) d))
    (b : Bool) :
    ((μ.restrict E).compProd (physicalObservedMixture hL g m t r R C S u particle hxy ν b)) univ=μ E := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
