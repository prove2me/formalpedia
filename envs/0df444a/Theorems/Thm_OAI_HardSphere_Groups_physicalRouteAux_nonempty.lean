-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physicalRouteAux_nonempty
-- name    : OAI.HardSphere.Groups.physicalRouteAux_nonempty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:44:54.784543+00:00
-- url     : https://prove2.me/theorems/2dd71323-154a-4523-af2a-42e727cd76f9
-- title:
--   OAI.HardSphere.Groups.physicalRouteAux_nonempty: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital`):
--
--   ```lean
--   lemma physicalRouteAux_nonempty (ht : 0<t)
--       (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
--       (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
--       (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
--       (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
--       Nonempty (PhysicalRouteAux hL g m t r R C S u particle labels v steps d)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectPoint`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.PhysicalRouteAux`, `OAI.HardSphere.Groups.datumAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.datumIndividualReference`, `OAI.HardSphere.Groups.routeCellPeriod`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.Groups.physicalTagged_observed_moment` and `OAI.HardSphere.Groups.physical_common_observed_estimates` of this split import it.
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

omit [Fintype J] in
lemma physicalRouteAux_nonempty (ht : 0<t)
    (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
    (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
    (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)
    (hp : ∀j,IsProbabilityMeasure (datumIndividualReference hL g m r R C S t u (particle j) d)) :
    Nonempty (PhysicalRouteAux hL g m t r R C S u particle labels v steps d) := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
