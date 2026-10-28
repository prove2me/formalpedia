-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physical_ground_bad_supply
-- name    : OAI.HardSphere.Groups.physical_ground_bad_supply
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:56:20.509019+00:00
-- url     : https://prove2.me/theorems/202d2c5e-6ef8-4342-ab8e-3cc4eba45b56
-- title:
--   OAI.HardSphere.Groups.physical_ground_bad_supply: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped ENNReal BigOperators Topology`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital`):
--
--   ```lean
--   theorem physical_ground_bad_supply :
--       ∃A ell b H t₀ : ℝ,2≤A ∧ 0<ell ∧ 0<b ∧ 0<H ∧ 0<t₀ ∧
--       ∀t : ℝ,0<t → t≤t₀ → ∀p : ℝ,0<p → p≤1 →
--       ∃D₀ : ℝ,1≤D₀ ∧ ∀{N K q G : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length},
--       ∀hL : L.val=(K:ℝ),100≤L.val → ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
--       ∀w : Time,t*(w:ℝ)=D⁻¹ → (G*(2*q):ℝ)≤ell*D/2 →
--       ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ → ∀g : Fin G,∀T : Finset (Fin 3→Fin K),
--         physicalDatumLaw g ψ (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ))
--           (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (2*t) (prefixTime midpointTime w)
--           {d : PhysicalDatum N K (2*q) G L | T⊆datumBad hL g (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊)
--             t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (prefixTime midpointTime w) d}≤
--           (6*ENNReal.ofReal p+ENNReal.ofReal ((2/5:ℝ)^q))^T.card
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.midpointTime`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.datumBad`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable`, `OAI.HardSphere.Wiener.Time` and `OAI.HardSphere.Wiener.prefixTime` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.physicalDatumLaw` and `OAI.HardSphere.PathCutoff.meanCost` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.IsGroundVector`, `OAI.HardSphere.Jet`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.condensation_with_mixed` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.exposedPeriodSingle_finite _root_.OAI.HardSphere.Bridge.physicalEdges_fintype _root_.OAI.HardSphere.Groups.cellPathReference_probability _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.datumGroupReference_finite _root_.OAI.HardSphere.Groups.datumIndividualReference_finite _root_.OAI.HardSphere.Groups.datumPhysicalReference_finite _root_.OAI.HardSphere.Groups.endpointPair_finite _root_.OAI.HardSphere.Groups.labelOptionSpace _root_.OAI.HardSphere.Groups.physicalBranchLaw_sfinite _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalLabelAt_markov _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalPrimaryReference_finite _root_.OAI.HardSphere.Groups.physicalRouteFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedFactor_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedRoute_finite _root_.OAI.HardSphere.Groups.physicalSlotReference_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Groups.vertexPair_finite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal BigOperators Topology
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital
attribute [local instance] Classical.propDecidable

theorem physical_ground_bad_supply :
    ∃A ell b H t₀ : ℝ,2≤A ∧ 0<ell ∧ 0<b ∧ 0<H ∧ 0<t₀ ∧
    ∀t : ℝ,0<t → t≤t₀ → ∀p : ℝ,0<p → p≤1 →
    ∃D₀ : ℝ,1≤D₀ ∧ ∀{N K q G : ℕ} [Nontrivial (Fin N)] [NeZero K] {L : Length},
    ∀hL : L.val=(K:ℝ),100≤L.val → ∀D α : ℝ,D=(N:ℝ)/L.val^3 → D₀≤D → A/2≤α → α≤2*A →
    ∀w : Time,t*(w:ℝ)=D⁻¹ → (G*(2*q):ℝ)≤ell*D/2 →
    ∀ψ : Jet N L,IsGroundVector N L (α/D) ψ → ∀g : Fin G,∀T : Finset (Fin 3→Fin K),
      physicalDatumLaw g ψ (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊) (α/D) (D^(1/12:ℝ))
        (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (b*D^(-(1/3):ℝ)) (2*t) (prefixTime midpointTime w)
        {d : PhysicalDatum N K (2*q) G L | T⊆datumBad hL g (⌈t/(α/D)^2⌉₊+⌈t/(α/D)^2⌉₊)
          t (α/D) (D^(1/12:ℝ)) (64*(meanCost+1)) (b*D^(-(1/3):ℝ)/8) (prefixTime midpointTime w) d}≤
        (6*ENNReal.ofReal p+ENNReal.ofReal ((2/5:ℝ)^q))^T.card := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
