-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_grid_close_tail
-- name    : OAI.HardSphere.Groups.grid_close_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:52:33.822234+00:00
-- url     : https://prove2.me/theorems/df4be02f-a47b-43c1-9143-2211c5b80c74
-- title:
--   OAI.HardSphere.Groups.grid_close_tail: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal NNReal Topology BigOperators`, `open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice`):
--
--   ```lean
--   lemma grid_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
--       ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
--         Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
--       ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
--       ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
--         100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
--       ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
--       ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (Fin 3→Fin K)),
--         groundPathLaw n L (α/D) T g {ω | ∀ v∈A,
--           θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω q)).card:ℝ)}≤
--           ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.localCloseLabels`, `OAI.HardSphere.CellOrbital.gridCenter` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.spatialCloseScale` (definitions bundle `OAIQ054H001` of this split); `OAI.HardSphere.groundPathLaw` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_ground_bad_supply` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
namespace HardSphere.Groups
open Wiener PathCutoff CellOrbital BathSlice HardSphere.Lattice

lemma grid_close_tail : ∃ Q : ℕ, 0<Q ∧ ∀ θ : ℝ, 0<θ →
    ∃ b Gθ : ℝ, 0<b ∧ b≤1/4 ∧ 0<Gθ ∧
      Tendsto (fun D : ℝ ↦ ((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ))) atTop (𝓝 0) ∧
    ∀ αmax : ℝ, ∃ D₀ : ℝ, 1≤D₀ ∧
    ∀ (n K : ℕ) [Nontrivial (Fin n)] (L : Length) (_hL : L.val=(K:ℝ)) (D α : ℝ),
      100≤L.val → D=(n:ℝ)/L.val^3 → D₀≤D → 1≤α → α≤αmax →
    ∀ (g : Jet n L), IsGroundVector n L (α/D) g →
    ∀ (T : ℝ), 0≤T → ∀ (q : Time) (A : Finset (Fin 3→Fin K)),
      groundPathLaw n L (α/D) T g {ω | ∀ v∈A,
        θ*D≤((localCloseLabels L (spatialCloseScale D b) (gridCenter L v) (ω q)).card:ℝ)}≤
        ENNReal.ofReal (((((Gθ/b^2)*D^(-(4/3):ℝ))^(1/(Q:ℝ)))^A.card)) := by
  sorry

end HardSphere.Groups

end
end

end

end OAI
end
