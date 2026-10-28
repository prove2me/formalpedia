-- Prove2me | Theorems.Thm_OAI_HardSphere_killedTransition_norm_le_of_energy
-- name    : OAI.HardSphere.killedTransition_norm_le_of_energy
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:01:00.987333+00:00
-- url     : https://prove2.me/theorems/39b2743a-0bd0-43ae-9570-2395ccdc2f04
-- title:
--   OAI.HardSphere.killedTransition_norm_le_of_energy: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators`, `open MeasureTheory ProbabilityTheory Real Complex`, `open scoped ENNReal ComplexConjugate`, `open ProbabilityTheory`, `open ContinuousLinearMap`):
--
--   ```lean
--   lemma killedTransition_norm_le_of_energy {N : ℕ} {L : Length} {a b t : ℝ} (ht : 0<t)
--       (henergy : ∀ u : Jet N L, u∈dirichletDomain N L a → b*‖u.1‖^2≤energy u) :
--       ‖killedTransition N L a t‖≤Real.exp (-t*b)
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.killedTransition` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length`, `OAI.HardSphere.ScalarL2`, `OAI.HardSphere.Torus`, `OAI.HardSphere.dirichletDomain`, `OAI.HardSphere.energy` and `OAI.HardSphere.lengthPositive` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.ground_product_one_add` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.gaussianCoordinates_probability _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
namespace HardSphere
open ContinuousLinearMap

lemma killedTransition_norm_le_of_energy {N : ℕ} {L : Length} {a b t : ℝ} (ht : 0<t)
    (henergy : ∀ u : Jet N L, u∈dirichletDomain N L a → b*‖u.1‖^2≤energy u) :
    ‖killedTransition N L a t‖≤Real.exp (-t*b) := by
  sorry

end HardSphere

end

end OAI
end
