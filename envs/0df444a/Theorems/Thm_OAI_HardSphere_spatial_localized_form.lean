-- Prove2me | Theorems.Thm_OAI_HardSphere_spatial_localized_form
-- name    : OAI.HardSphere.spatial_localized_form
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:04:08.36505+00:00
-- url     : https://prove2.me/theorems/d45c2721-58f5-4949-8eb3-76b01c4e660c
-- title:
--   OAI.HardSphere.spatial_localized_form: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`, `open scoped BigOperators ComplexConjugate`, `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal NNReal Topology BigOperators`, `open MeasureTheory ProbabilityTheory Real Complex`, `open scoped ENNReal ComplexConjugate`, `open ProbabilityTheory`, `open MeasureTheory Filter Set`, `open scoped ENNReal Topology`, `open MeasureTheory Set`, `open scoped ENNReal`, `open MeasureTheory Set Filter SphericalCoordinates`, `open scoped ENNReal`):
--
--   ```lean
--   theorem spatial_localized_form : ∃ C c : ℝ, 0< C ∧ 0< c ∧
--       ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r b D : ℝ),
--         D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< b →
--         2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤ L.val →
--         (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
--       ∀ (g : Jet n L), IsGroundVector n L r g →
--       ∀ (A : Finset (Torus L)) (u : Jet n L), u∈dirichletDomain n L r →
--         (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
--           c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)≤
--           energy u-energy g*‖u.1‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.spatialCloseScale` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.localizedNearLabels` and `OAI.HardSphere.weightedSiteCount` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length`, `OAI.HardSphere.ScalarL2`, `OAI.HardSphere.Torus`, `OAI.HardSphere.dirichletDomain`, `OAI.HardSphere.energy` and `OAI.HardSphere.lengthPositive` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.BathSlice.physical_close_tail` and `OAI.HardSphere.Groups.grid_close_tail` of this split import it.
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
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
namespace HardSphere
open MeasureTheory Set Filter SphericalCoordinates
open scoped ENNReal

theorem spatial_localized_form : ∃ C c : ℝ, 0< C ∧ 0< c ∧
    ∀ (n K : ℕ) (L : Length) ( _hL : L.val=(K:ℝ)) (r b D : ℝ),
      D=(n:ℝ)/L.val^3 → 1≤ D → 1≤ D*r → 0< r → 0< b →
      2*spatialCloseScale D b≤1 → 10*spatialCloseScale D b≤ L.val →
      (n:ℝ)*(2*Real.pi*r)^3≤ L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g →
    ∀ (A : Finset (Torus L)) (u : Jet n L), u∈dirichletDomain n L r →
      (D*r)*(∫ X, (weightedSiteCount L A X-C*D*(A.card:ℝ)+
        c/b^3*((localizedNearLabels L A (spatialCloseScale D b) X).card:ℝ))*‖u.1 X‖^2)≤
        energy u-energy g*‖u.1‖^2 := by
  sorry

end HardSphere

end

end OAI
end
