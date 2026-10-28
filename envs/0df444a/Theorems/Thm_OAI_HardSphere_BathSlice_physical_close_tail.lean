-- Prove2me | Theorems.Thm_OAI_HardSphere_BathSlice_physical_close_tail
-- name    : OAI.HardSphere.BathSlice.physical_close_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:50:21.18516+00:00
-- url     : https://prove2.me/theorems/2e097b2c-dbba-408a-9c0d-c5cb490e1ef8
-- title:
--   OAI.HardSphere.BathSlice.physical_close_tail: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.BathSlice`, with `open MeasureTheory Filter Set`, `open scoped ENNReal Topology BigOperators`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical`, `open scoped BigOperators Classical ENNReal`, `open MeasureTheory Set Filter HardSphere.Lattice`):
--
--   ```lean
--   theorem physical_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
--       ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
--         Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
--       ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
--       ∀ (n K : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
--         100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
--       ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
--       ∀ (m : ℕ) (e : Fin m ↪ Fin n) (A : Finset (DiscreteTorus K)),
--         ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
--           {Y | A ⊆ closeSet L (spatialCloseScale D b) (θ*D) Y} ≤
--           (ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))))^A.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.BathSlice.closeSet` and `OAI.HardSphere.Lattice.DiscreteTorus` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.spatialCloseScale` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.groundPositionLaw` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.physical_uniform_phase_error` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.freePathLaw_finite_deletion _root_.OAI.HardSphere.killedPathLaw_finite_deletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical ENNReal
namespace HardSphere.BathSlice
open MeasureTheory Set Filter HardSphere.Lattice

theorem physical_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [NeZero K] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), HardSphere.IsGroundVector n L (α/D) g →
    ∀ (m : ℕ) (e : Fin m ↪ Fin n) (A : Finset (DiscreteTorus K)),
      ((groundPositionLaw n L g).map (fun X i ↦ X (e i)))
        {Y | A ⊆ closeSet L (spatialCloseScale D b) (θ*D) Y} ≤
        (ENNReal.ofReal (((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))))^A.card := by
  sorry

end HardSphere.BathSlice

end

end OAI
end
