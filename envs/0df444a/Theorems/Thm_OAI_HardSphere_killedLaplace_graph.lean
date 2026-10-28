-- Prove2me | Theorems.Thm_OAI_HardSphere_killedLaplace_graph
-- name    : OAI.HardSphere.killedLaplace_graph
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:59:52.481224+00:00
-- url     : https://prove2.me/theorems/c766c233-f538-4f2b-a69c-42ecf6103fea
-- title:
--   OAI.HardSphere.killedLaplace_graph: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators`, `open MeasureTheory ProbabilityTheory Real Complex`, `open scoped ENNReal ComplexConjugate`, `open MeasureTheory Set Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma killedLaplace_graph (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
--       ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L a f ∧
--         ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.HilbertJet`, `OAI.HardSphere.scalarL2_addCommMonoid` and `OAI.HardSphere.scalarL2_module` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.hilbertDomain`, `OAI.HardSphere.killedLaplace` and `OAI.HardSphere.scalarEmbedding` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.Length`, `OAI.HardSphere.ScalarL2`, `OAI.HardSphere.Torus` and `OAI.HardSphere.lengthPositive` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.BathSlice.IsGroundVector.bathLaw_ae_allowed`, `OAI.HardSphere.IsGroundVector.ae_killed_complexPhase`, `OAI.HardSphere.IsGroundVector.groundPathLaw_marginal`, `OAI.HardSphere.IsGroundVector.groundPathLaw_probability` and `OAI.HardSphere.killedTransition_norm_le_of_energy` of this split import it.
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
namespace HardSphere
open MeasureTheory Set Filter
open scoped Topology

lemma killedLaplace_graph (N : ℕ) (L : Length) (a : ℝ) (f : ScalarL2 N L) :
    ∃ v : hilbertDomain N L a, scalarEmbedding N L a v=killedLaplace N L a f ∧
      ‖v‖^2≤(1+4*Real.exp 1)*‖f‖^2 := by
  sorry

end HardSphere

open ProbabilityTheory

end

end OAI
end
