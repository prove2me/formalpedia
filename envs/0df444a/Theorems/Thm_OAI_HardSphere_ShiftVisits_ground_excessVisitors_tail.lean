-- Prove2me | Theorems.Thm_OAI_HardSphere_ShiftVisits_ground_excessVisitors_tail
-- name    : OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T20:02:05.339331+00:00
-- url     : https://prove2.me/theorems/1dc341de-f93e-4cd3-9714-30220f113f02
-- title:
--   OAI.HardSphere.ShiftVisits.ground_excessVisitors_tail: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.ShiftVisits`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal NNReal Topology BigOperators`, `open Wiener PathCutoff BathSlice HardSphere.Lattice CellOrbital HardSphere.FreeVisits`):
--
--   ```lean
--   theorem ground_excessVisitors_tail :
--       ∃ αstar : ℝ, 0<αstar ∧ ∀ αmax : ℝ, 0<αmax →
--       ∃ H : ℝ, 0<H ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
--       ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → D*r≤αmax → 0 < r →
--         (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
--       ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (x₀ : Torus L) (A : Finset (DiscreteTorus K)) {t : ℝ},
--         0<t → t≤2 →
--         groundPathLaw n L r t g {ω | ∀v∈A,H*D≤(visitorCount L x₀ Set.univ v ω:ℝ)}≤
--           ENNReal.ofReal (Real.exp (-(D*(A.card:ℝ))))
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable` and `OAI.HardSphere.Lattice.DiscreteTorus` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.groundPathLaw` and `OAI.HardSphere.ShiftVisits.visitorCount` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_ground_bad_supply` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedBridgeKernel_markov _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.exposedTrialKernel_markov _root_.OAI.HardSphere.Bridge.instBorelSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.instIsProbabilityMeasureNoiseLaw _root_.OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint _root_.OAI.HardSphere.Bridge.parameterBridgeKernel_markov _root_.OAI.HardSphere.Bridge.parameterIndividualReference_finite _root_.OAI.HardSphere.Bridge.parameterTrialKernel_markov _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Bridge.trialKernel_markov _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalAllocationKernel_markov _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Lattice.environmentMeasurableSpace _root_.OAI.HardSphere.Lattice.simplePathCountable _root_.OAI.HardSphere.Lattice.simplePathMeasurableSpace _root_.OAI.HardSphere.Rescaling.config_haar _root_.OAI.HardSphere.bridgeEndpointBase_finite _root_.OAI.HardSphere.coordinateBridge_probability _root_.OAI.HardSphere.endpointWeightedBase_sfinite _root_.OAI.HardSphere.gaussianCoordinates_probability
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
namespace HardSphere.ShiftVisits
open Wiener PathCutoff BathSlice HardSphere.Lattice CellOrbital HardSphere.FreeVisits

theorem ground_excessVisitors_tail :
    ∃ αstar : ℝ, 0<αstar ∧ ∀ αmax : ℝ, 0<αmax →
    ∃ H : ℝ, 0<H ∧ ∀ (n K : ℕ) [NeZero K] (L : Length), L.val=(K:ℝ) →
    ∀ r D : ℝ, D=(n:ℝ)/L.val^3 → 1≤D → αstar≤D*r → D*r≤αmax → 0 < r →
      (n:ℝ)*(2*Real.pi*r)^3≤L.val^3/2 →
    ∀ (g : Jet n L), IsGroundVector n L r g → ∀ (x₀ : Torus L) (A : Finset (DiscreteTorus K)) {t : ℝ},
      0<t → t≤2 →
      groundPathLaw n L r t g {ω | ∀v∈A,H*D≤(visitorCount L x₀ Set.univ v ω:ℝ)}≤
        ENNReal.ofReal (Real.exp (-(D*(A.card:ℝ)))) := by
  sorry

end HardSphere.ShiftVisits

end
end

end

end OAI
end
