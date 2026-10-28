-- Prove2me | Theorems.Thm_OAI_HardSphere_Groups_physicalBranchLaw_collision
-- name    : OAI.HardSphere.Groups.physicalBranchLaw_collision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T19:55:36.776982+00:00
-- url     : https://prove2.me/theorems/9fd754a6-9001-4fd5-93fd-eed5e9de5920
-- title:
--   OAI.HardSphere.Groups.physicalBranchLaw_collision: intermediate lemma from OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HardSphere.condensation_with_mixed`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Ground-state condensation in the dilute hard-sphere gas (result family 267)*, OpenAI Math Release, September 24, 2026, result family 267, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HardSphere.Groups`, with `open MeasureTheory ProbabilityTheory Set`, `open scoped ENNReal`, `open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice`):
--
--   ```lean
--   theorem physicalBranchLaw_collision {N K M G m : ℕ} {L : Length}
--       (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val) (hm : 0 < m)
--       (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
--       (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
--       (t r R C S s₀ h : ℝ) (u : Time)
--       (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hR : 0≤R) (hC : 0≤C) (hh : 0<h)
--       (hu : (u:ℝ)=h/(2*t)) (hsmall : r*R≤1) (hsep : r + 2*S ≤ s₀)
--       (hτr : (2*t)/(m:ℝ) ≤ r^2) (hmscale : (m:ℝ)*r^2≤2*(2*t))
--       (hwindow : 2*((2*t)/(m:ℝ))≤h) (hlarge : 8*(2*t)≤(m:ℝ)*h) (hdrift : 26/(m:ℝ) ≤ r) :
--       ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
--         ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u (branchParticles g a) d (some k),
--           physicalCollisionReference hL g m t r R C S u (branchParticles g a) d j
--             {p | TrialCollision r (projectCurve L f.val) p.val}≤datumCollisionBound t r h R C
--   ```
--
--   **Definitions.** The statement is written with `OAI.HardSphere.BridgeEndpoints`, `OAI.HardSphere.ConfigurationPath`, `OAI.HardSphere.configurationPathMeasurable`, `OAI.HardSphere.Bridge.TrialCollision`, `OAI.HardSphere.Bridge.instMeasurableSpaceContinuousMapElemRealTimePoint`, `OAI.HardSphere.Bridge.projectCurve`, `OAI.HardSphere.GaussianPacking.Point`, `OAI.HardSphere.Groups.GridAllocation`, `OAI.HardSphere.Groups.PhysicalDatum`, `OAI.HardSphere.Groups.branchParticles`, `OAI.HardSphere.Groups.groupUnion`, `OAI.HardSphere.Groups.physicalCollisionReference`, `OAI.HardSphere.Groups.physicalSlotAllowed`, `OAI.HardSphere.Sampling.Allocation`, `OAI.HardSphere.Sampling.allocationMeasurable` and `OAI.HardSphere.Wiener.Time` (definitions bundle `OAIQ054H000` of this split); `OAI.HardSphere.Groups.datumCollisionBound` and `OAI.HardSphere.Groups.physicalBranchLaw` (definitions bundle `OAIQ054H002` of this split); `OAI.HardSphere.Configuration`, `OAI.HardSphere.Direction`, `OAI.HardSphere.Length` and `OAI.HardSphere.Torus` (the published bundle `Def_HardSphere`).
--
--   **Used by.** The proof of `OAI.HardSphere.Groups.physical_group_common_comparison` of this split imports it.
-- source:
--   OpenAI, Ground-state condensation in the dilute hard-sphere gas (result family 267), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 267; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Ground-state-condensation-in-the-dilute-hard-sphere-gas-September-24-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_HardSphere
import Definitions.Def_OAIQ054H002

section

attribute [-instance] _root_.OAI.HardSphere.Bridge.targetUniform_finite _root_.OAI.HardSphere.Groups.cellPointReference_probability _root_.OAI.HardSphere.Groups.physicalFamilyReference_finite _root_.OAI.HardSphere.Groups.physicalOnPrimary_finite _root_.OAI.HardSphere.Groups.physicalPairedRoute_finite _root_.OAI.HardSphere.Groups.physicalSelectedOn_finite _root_.OAI.HardSphere.Groups.physicalSharedOn_finite _root_.OAI.HardSphere.Groups.physicalTaggedReference_finite _root_.OAI.HardSphere.Groups.rawPhysicalBranch_sfinite _root_.OAI.HardSphere.Rescaling.config_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Groups
open Wiener Bridge Sampling Comparison GaussianPacking PathCutoff CellOrbital HardSphere.Lattice
attribute [local instance] Classical.propDecidable
attribute [local irreducible] datumHome datumSelected groupUnion datumStart datumEnd anchorPoint

theorem physicalBranchLaw_collision {N K M G m : ℕ} {L : Length}
    (hL : L.val=(K:ℝ)) (hK : 1≤K) (h50 : 50<L.val) (hm : 0 < m)
    (μ : Measure (BridgeEndpoints N L)) [SFinite μ]
    (g : Fin G) (b : Fin N→Bool) (a : GridAllocation N K (G*M))
    (t r R C S s₀ h : ℝ) (u : Time)
    (ht : 0<t) (hr : 0 < r) (hr1 : r≤1) (hR : 0≤R) (hC : 0≤C) (hh : 0<h)
    (hu : (u:ℝ)=h/(2*t)) (hsmall : r*R≤1) (hsep : r + 2*S ≤ s₀)
    (hτr : (2*t)/(m:ℝ) ≤ r^2) (hmscale : (m:ℝ)*r^2≤2*(2*t))
    (hwindow : 2*((2*t)/(m:ℝ))≤h) (hlarge : 8*(2*t)≤(m:ℝ)*h) (hdrift : 26/(m:ℝ) ≤ r) :
    ∀ᵐd ∂physicalBranchLaw hL μ g b a m r R C S s₀ (2*t) u,
      ∀ j k, j ≠ k → ∀f : physicalSlotAllowed hL g m r R C S u (branchParticles g a) d (some k),
        physicalCollisionReference hL g m t r R C S u (branchParticles g a) d j
          {p | TrialCollision r (projectCurve L f.val) p.val}≤datumCollisionBound t r h R C := by
  sorry

end HardSphere.Groups
end
end

end OAI
end
