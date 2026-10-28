-- Prove2me | Theorems.Thm_OAI_HardSphere_IsGroundVector_groundPathLaw_probability
-- name    : OAI.HardSphere.IsGroundVector.groundPathLaw_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:58:50.735445+00:00
-- url     : https://prove2.me/theorems/8128418c-f464-4db6-9012-0508649113cf
-- title:
--   OAI.HardSphere.IsGroundVector.groundPathLaw_probability: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open MeasureTheory Filter Set`, `open scoped Topology ENNReal BigOperators`, `open scoped RealInnerProductSpace`, `open MeasureTheory Wiener Set Filter`, `open scoped ComplexConjugate`):
--
--   ```lean
--   lemma IsGroundVector.groundPathLaw_probability {u : Jet N L} (hu : IsGroundVector N L a u)
--       (ht : 0 ≤ t) : IsProbabilityMeasure (groundPathLaw N L a t u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath` and `OAI.HardSphere.configurationPathMeasurable` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.groundPathLaw` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet` and `OAI.HardSphere.Length` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.Groups.physical_ground_bad_supply`, `OAI.HardSphere.Groups.physical_group_common_comparison`, `OAI.HardSphere.Groups.physical_modulus_from_gains`, `OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail`, `OAI.HardSphere.ShiftVisits.ground_longVisitors_tail`, `OAI.HardSphere.ShiftVisits.interacting_visit_mgf_uniform` and `OAI.HardSphere.condensation_with_mixed` of this split import it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators
open scoped RealInnerProductSpace
namespace HardSphere
open MeasureTheory Wiener Set Filter
open scoped ComplexConjugate
noncomputable section
variable {N : ℕ} {L : Length} {a t : ℝ}

lemma IsGroundVector.groundPathLaw_probability {u : Jet N L} (hu : IsGroundVector N L a u)
    (ht : 0 ≤ t) : IsProbabilityMeasure (groundPathLaw N L a t u) := by
  sorry

end
end HardSphere

end
end
end

end OAI
end
