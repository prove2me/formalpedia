-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physical_second_likelihood_moment
-- name    : OAI.HardSphere.Groups.physical_second_likelihood_moment
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:58:43.613546+00:00
-- url     : https://prove2.me/theorems/188cad4c-3ee6-4314-850a-84d672d248bb
-- title:
--   OAI.HardSphere.Groups.physical_second_likelihood_moment: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice`):
--
--   ```lean
--   theorem physical_second_likelihood_moment {N K M G n l : ℕ} [NeZero K] {L : Length}
--       (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
--       (particle : J↪Fin N)
--       (f : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K)) (steps : Fin (n+1)→Fin 7)
--       (f' : Fin (l+1)↪J) (v' : Fin (l+2)→(Fin 3→Fin K)) (steps' : Fin (l+1)→Fin 7)
--       (d : PhysicalDatum N K M G L)
--       (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
--       (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
--       (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
--       (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
--       (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
--       (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
--       (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
--       (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
--       (hn : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
--       (hn' : ∀k : Fin (l+1),torusDistance L (gridCenter L (v' k.castSucc)) (gridCenter L (v' k.succ))≤1)
--       (hstart : v' 0=v 0)
--       (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
--       (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
--       (q a : ℝ≥0∞) (ha0 : 0<a)
--       (hq : ∀ j k, j ≠ k → ∀p : physicalSlotAllowed hL g m r R C S u particle d (some k),
--         physicalCollisionReference hL g m t r R C S u particle d j
--           {p' | TrialCollision r (projectCurve L p.val) p'.val}≤q)
--       (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
--       let c := fun i ↦ gridSite (slotCenter (fun j ↦ datumHome hL d (particle j)) (v 0) i)
--       let ns := nearSlots (torusNear K 30) c (routeSlots f) (routeSlots f')
--       let nt := nearSlots (torusNear K 30) c (routeSlots f') (routeSlots f)
--       (∫⁻x,A.secondDensity x*B.secondDensity x
--         ∂physicalOnPrimary hL g m t r R C S u particle (v 0) d)≤
--         (routeDensityBound t)^(routeSlots f∩routeSlots f').card/a^(2*(ns.card+nt.card))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.TrialCollision`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectCurve`, `OAI.HardSphere.Bridge.projectPoint`, `OAI.HardSphere.CellOrbital.gridCenter`, `OAI.HardSphere.Comparison.nearSlots`, `OAI.HardSphere.Comparison.routeSlots`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.PhysicalRouteAux`, `OAI.HardSphere.Groups.datumAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.datumIndividualReference`, `OAI.HardSphere.Groups.physicalCollisionReference`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Groups.routeCellPeriod`, `OAI.HardSphere.Groups.routeDensityBound`, `OAI.HardSphere.Lattice.DiscreteTorus`, `OAI.HardSphere.Lattice.torusNear`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable`, `OAI.HardSphere.Wiener.Time` and `OAI.HardSphere.Groups.PhysicalRouteAux.secondDensity` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.slotCenter` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.Groups.gridSite` and `OAI.HardSphere.Groups.physicalOnPrimary` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length`, `OAI.HardSphere.Torus` and `OAI.HardSphere.torusDistance` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physicalTagged_observed_moment` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

end HardSphere.Groups
end
end

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
variable {J : Type*} [Fintype J] [DecidableEq J]

theorem physical_second_likelihood_moment {N K M G n l : ℕ} [NeZero K] {L : Length}
    (hL : L.val=(K:ℝ)) (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (u : Time)
    (particle : J↪Fin N)
    (f : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K)) (steps : Fin (n+1)→Fin 7)
    (f' : Fin (l+1)↪J) (v' : Fin (l+2)→(Fin 3→Fin K)) (steps' : Fin (l+1)→Fin 7)
    (d : PhysicalDatum N K M G L)
    (A : PhysicalRouteAux hL g m t r R C S u particle f v steps d)
    (B : PhysicalRouteAux hL g m t r R C S u particle f' v' steps' d)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hc' : ∀k,projectPoint L (routeCellPeriod (v' k.succ) (v' k.castSucc) (steps' k))=0)
    (hh : ∀k,datumHome hL d (particle (f k))=v k.castSucc)
    (hh' : ∀k,datumHome hL d (particle (f' k))=v' k.castSucc)
    (ha : ∀k,datumAccessible hL g m t r R C S u (particle (f k)) d)
    (ha' : ∀k,datumAccessible hL g m t r R C S u (particle (f' k)) d)
    (hn : ∀k : Fin (n+1),torusDistance L (gridCenter L (v k.castSucc)) (gridCenter L (v k.succ))≤1)
    (hn' : ∀k : Fin (l+1),torusDistance L (gridCenter L (v' k.castSucc)) (gridCenter L (v' k.succ))≤1)
    (hstart : v' 0=v 0)
    (hm : ∀w,(Finset.univ.filter (fun j ↦ datumHome hL d (particle j)=w)).card≤M)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d))
    (q a : ℝ≥0∞) (ha0 : 0<a)
    (hq : ∀ j k, j ≠ k → ∀p : physicalSlotAllowed hL g m r R C S u particle d (some k),
      physicalCollisionReference hL g m t r R C S u particle d j
        {p' | TrialCollision r (projectCurve L p.val) p'.val}≤q)
    (hsmall : a+(4*(49^3*(M+1)):ℕ)*(routeDensityBound t*q)≤1) :
    let c := fun i ↦ gridSite (slotCenter (fun j ↦ datumHome hL d (particle j)) (v 0) i)
    let ns := nearSlots (torusNear K 30) c (routeSlots f) (routeSlots f')
    let nt := nearSlots (torusNear K 30) c (routeSlots f') (routeSlots f)
    (∫⁻x,A.secondDensity x*B.secondDensity x
      ∂physicalOnPrimary hL g m t r R C S u particle (v 0) d)≤
      (routeDensityBound t)^(routeSlots f∩routeSlots f').card/a^(2*(ns.card+nt.card)) := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
