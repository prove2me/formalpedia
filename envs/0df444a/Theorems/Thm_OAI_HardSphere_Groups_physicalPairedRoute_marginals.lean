-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physicalPairedRoute_marginals
-- name    : OAI.HardSphere.Groups.physicalPairedRoute_marginals
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:52:48.372984+00:00
-- url     : https://prove2.me/theorems/5c2cf2ba-1e50-4200-850e-ccf964e5e51f
-- title:
--   OAI.HardSphere.Groups.physicalPairedRoute_marginals: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal NNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital`):
--
--   ```lean
--   lemma physicalPairedRoute_marginals :
--       (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.fst=
--         ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
--           (ambientFirst (routeSlots labels) (routePermutation labels))).map
--             (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ∧
--       (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.snd=
--         ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
--           (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))).map
--             (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectPoint`, `OAI.HardSphere.Comparison.ambientFirst`, `OAI.HardSphere.Comparison.ambientSecond`, `OAI.HardSphere.Comparison.routeConfigMap`, `OAI.HardSphere.Comparison.routePermutation`, `OAI.HardSphere.Comparison.routePermutation_fixed`, `OAI.HardSphere.Comparison.routeSlots`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.datumAccessible`, `OAI.HardSphere.Groups.datumHome`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Groups.routeCellPeriod`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.physicalPairedRoute` and `OAI.HardSphere.Groups.physicalSharedOn` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.Groups.physicalTagged_observed_moment` and `OAI.HardSphere.Groups.physical_common_observed_estimates` of this split import it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
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
variable {J : Type*} [Fintype J] [DecidableEq J]
variable {N K M G n : ℕ} {L : Length} (hL : L.val=(K:ℝ))
  (g : Fin G) (m : ℕ) (t r R C S : ℝ) (ht : 0<t) (hr : r≤1) (u : Time)
  (particle : J↪Fin N) (labels : Fin (n+1)↪J) (v : Fin (n+2)→Fin 3→Fin K)
  (steps : Fin (n+1)→Fin 7)
  (hc : ∀k,projectPoint L (routeCellPeriod (v k.succ) (v k.castSucc) (steps k))=0)
  (d : PhysicalDatum N K M G L)
  (hhome : ∀k,datumHome hL d (particle (labels k))=v k.castSucc)
  (haccess : ∀k,datumAccessible hL g m t r R C S u (particle (labels k)) d)

include ht hr hc hhome haccess

lemma physicalPairedRoute_marginals :
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.fst=
      ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
        (ambientFirst (routeSlots labels) (routePermutation labels))).map
          (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) ∧
    (physicalPairedRoute hL g m t r R C S u particle labels v steps d).map Prod.snd=
      ((physicalSharedOn hL g m t r R C S u particle labels v steps d).map
        (ambientSecond (routeSlots labels) (routePermutation labels) (routePermutation_fixed labels))).map
          (routeConfigMap (fun i ↦ (Subtype.val : physicalSlotAllowed hL g m r R C S u particle d i→_))) := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
