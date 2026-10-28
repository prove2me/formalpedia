-- Prove2me | Theorems.Thm_OAI_HardSphere_ground_product_one_add
-- name    : OAI.HardSphere.ground_product_one_add
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:02:15.61306+00:00
-- url     : https://prove2.me/theorems/2aa385a8-5331-4730-b7cb-7608e9b7a776
-- title:
--   OAI.HardSphere.ground_product_one_add: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere`, with `open scoped BigOperators`, `open MeasureTheory Set Filter`, `open scoped ENNReal NNReal Topology`, `open Wiener`):
--
--   ```lean
--   lemma ground_product_one_add : ∃ C : ℝ, 0<C ∧
--       ∀ (N : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
--       (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
--       ∀ u : Jet N L, IsGroundVector N L r u →
--       ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
--       (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
--         (∫⁻ ω : ConfigurationPath N L, ∏i, (1+h (onePathAt i ω)) ∂groundPathLaw N L r t u) ≤
--           ∫⁻ X : Configuration N L, ∏i,(1+ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))*
--             oneFreeExpectation t h (X i)) ∂groundPositionLaw N L u
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.onePathAt` and `OAI.HardSphere.reverseConfigurationPath` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.groundPathLaw`, `OAI.HardSphere.groundPositionLaw` and `OAI.HardSphere.oneFreeExpectation` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proofs of `OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail`, `OAI.HardSphere.ShiftVisits.ground_longVisitors_tail` and `OAI.HardSphere.ShiftVisits.interacting_visit_mgf_uniform` of this split import it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open scoped BigOperators
namespace HardSphere

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open Wiener

lemma ground_product_one_add : ∃ C : ℝ, 0<C ∧
    ∀ (N : ℕ) (L : Length) (r t : ℝ), 0 < r → 0<t →
    (N:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ u : Jet N L, IsGroundVector N L r u →
    ∀ h : ConfigurationPath 1 L → ℝ≥0∞, Measurable h →
    (∀ ω,h (reverseConfigurationPath 1 L ω)=h ω) →
      (∫⁻ ω : ConfigurationPath N L, ∏i, (1+h (onePathAt i ω)) ∂groundPathLaw N L r t u) ≤
        ∫⁻ X : Configuration N L, ∏i,(1+ENNReal.ofReal (Real.exp (t*C*(N:ℝ)*r/L.val^3))*
          oneFreeExpectation t h (X i)) ∂groundPositionLaw N L u := by
  sorry

end HardSphere

end
end

end

end OAI
end
