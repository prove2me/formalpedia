-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_PhysicalRouteAux_path_bounds
-- name    : OAI.HardSphere.Groups.PhysicalRouteAux.path_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:44:24.110983+00:00
-- url     : https://prove2.me/theorems/0926b8b5-a341-4f63-9e9d-ca89176d221b
-- title:
--   OAI.HardSphere.Groups.PhysicalRouteAux.path_bounds: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital`):
--
--   ```lean
--   lemma PhysicalRouteAux.path_bounds (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
--       (ht : 0<t)
--       (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
--       (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
--       (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
--       let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
--       let σ := routePermutation labels
--       let s := routeSlots labels
--       let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
--       let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
--       let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
--       (∀b j,routeOwner σ some b j∈s→
--         ((μ (routeOwner σ some b j)).compProd (A.forward (routeOwner σ some b j))).map
--           (routePath (X:=X) σ s (routePermutation_fixed labels) allowed some (fun _ f ↦ f) b j)≤
--             routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) ∧
--       (∀b j,routeOwner σ.symm some b j∈s→
--         ((ν (routeOwner σ.symm some b j)).compProd (A.backward (routeOwner σ.symm some b j))).map
--           (routePath (X:=X) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) allowed some (fun _ f ↦ f) b j)≤
--             routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectPoint`, `OAI.HardSphere.Bridge.reverse_fix`, `OAI.HardSphere.Bridge.routeOwner`, `OAI.HardSphere.Bridge.routePath`, `OAI.HardSphere.Comparison.routePermutation`, `OAI.HardSphere.Comparison.routePermutation_fixed`, `OAI.HardSphere.Comparison.routeSlots`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.PhysicalRouteAux`, `OAI.HardSphere.Groups.datumAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.physicalCollisionReference`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Groups.physicalSlotOn`, `OAI.HardSphere.Groups.routeCellPeriod`, `OAI.HardSphere.Groups.routeDensityBound` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.Groups.physical_first_likelihood_moment` and `OAI.HardSphere.Groups.physical_second_likelihood_moment` of this split import it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H000

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace
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
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
    (g : Fin G) (m : ℕ) (t r R C S : ℝ) (u : Time)
    (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→(Fin 3→Fin K))
    (steps : Fin (n+1)→Fin 7) (d : PhysicalDatum N K M G L)

attribute [instance] PhysicalRouteAux.forward_finite PhysicalRouteAux.backward_finite

variable {hL g m t r R C S u particle labels v steps d}

omit [Fintype J] in
lemma PhysicalRouteAux.path_bounds (A : PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
    (ht : 0<t)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d) :
    let X : Option J→Type := fun i ↦ physicalSlotAllowed hL g m r R C S u particle d i
    let σ := routePermutation labels
    let s := routeSlots labels
    let allowed := fun j ↦ physicalSlotAllowed hL g m r R C S u particle d (some j)
    let μ := physicalSlotOn hL g m t r R C S u particle (v (Fin.last (n+1))) d
    let ν := physicalSlotOn hL g m t r R C S u particle (v 0) d
    (∀b j,routeOwner σ some b j∈s→
      ((μ (routeOwner σ some b j)).compProd (A.forward (routeOwner σ some b j))).map
        (routePath (X:=X) σ s (routePermutation_fixed labels) allowed some (fun _ f ↦ f) b j)≤
          routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) ∧
    (∀b j,routeOwner σ.symm some b j∈s→
      ((ν (routeOwner σ.symm some b j)).compProd (A.backward (routeOwner σ.symm some b j))).map
        (routePath (X:=X) σ.symm s (reverse_fix σ s (routePermutation_fixed labels)) allowed some (fun _ f ↦ f) b j)≤
          routeDensityBound t • physicalCollisionReference hL g m t r R C S u particle d j) := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
