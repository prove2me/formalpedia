-- Prove2me | Theorems.Thm_OAI_CoulombAtom_TailTiltState_event_radial_comparison_of_cell
-- name    : OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:32:33.071806+00:00
-- url     : https://prove2.me/theorems/5d837c6e-f695-4c6b-b50f-d4d0835eca23
-- title:
--   OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell` of [lean/OAI/Analysis/CoulombIonization/Ionization/SharpEventLawJointComparisonCell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SharpEventLawJointComparisonCell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter Set Metric`, `open scoped BigOperators ENNReal ContDiff`, `open CoulombAnalysis`, `open MeasureTheory Filter Set Metric`, `open scoped BigOperators ENNReal ContDiff`, `open CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem TailTiltState.event_radial_comparison_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
--       (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
--       {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
--       (hstate : TailTiltState Z lam r K p₀ δ F)
--       {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
--       (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
--       (j : Fin (K+1)) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
--       (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y) {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
--       (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
--       (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
--       (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
--       {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
--       (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
--       (hprob : p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal) :
--       ∃ G : fermionGraph N, ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
--         ‖fermionGraphValue N G‖^2 = 1 ∧
--         graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
--           Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
--         radialPatchGapMean (graphFormVector G) y ht hb Z lam ≤
--           dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
--           sharpPatchRemainder (localCellRadius y) b
--             (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y) ∧
--         |Z/‖y‖-lam-(((physicalObservationLaw (graphRawLaw F) K) A).toReal)⁻¹*
--           (∫ z in A, tfPotential (jointMasterPosterior (graphRawLaw F)
--             (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
--             (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y
--               ∂physicalObservationLaw (graphRawLaw F) K)-
--           expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
--           sharpPotentialRemainder (localCellRadius y) b
--             (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
--             (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
--           sharpLocalPotentialBudget (localCellRadius y)
--             (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
--             (2*masterWidth c₁ r₀ s y)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.tfPotential`, `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.SectorHilbert`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.fermionGraphValue`, `OAI.CoulombAtom.fermionSpace`, `OAI.CoulombAtom.graphFormVector`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.masterWidth` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombObservation.dyadicObservationWidth` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.graphRawLaw` and `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.canonicalRealPacket` and `OAI.CoulombAtom.dyadicUniformEventBudget` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.expectedRadialPatchCenter`, `OAI.CoulombAtom.jointMasterPosterior`, `OAI.CoulombAtom.observationInformation`, `OAI.CoulombAtom.originalDatum` and `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.localOffsetMass` (definitions bundle `OAIQ071C007` of this split); `OAI.CoulombAtom.radialPatchGapMean` (definitions bundle `OAIQ071C008` of this split); `OAI.CoulombAtom.graphRawLaw_finite` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.TailTiltState`, `OAI.CoulombAtom.sharpLocalPotentialBudget`, `OAI.CoulombAtom.sharpPatchRemainder` and `OAI.CoulombAtom.sharpPotentialRemainder` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombAtom_TailTiltState_high_inverse_event_of_cell`, `OAI_CoulombAtom_TailTiltState_point_inverse_events_of_cell` and `OAI.CoulombAtom.actual_expandedAnnulus_inverse_uniform_eventually` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SharpEventLawJointComparisonCell.lean (declaration OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace CoulombAtom

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis

section
open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget
attribute [local irreducible] radialPatchGapMean expectedRadialPatchCenter corePriceExcess

theorem TailTiltState.event_radial_comparison_of_cell {Z lam r : ℝ} (hZ : 0 ≤ Z)
    (hlam : 0 < lam) {N K : ℕ} {F : fermionGraph N}
    {p₀ : Fin (K+1) → ℝ} {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j)
    (hstate : TailTiltState Z lam r K p₀ δ F)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    (hcell : 2*masterWidth c₁ r₀ s y ≤ 4*localCellRadius y) {b q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hq : 0 < q) (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hqR : q ≤ 3*(5*localCellRadius y-4*b)/4)
    (hcollar : localCellRadius y ≤ b^2*(1/(localCellRadius y)^3))
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r k) j] A)
    (hprob : p₀ j ≤ ((physicalObservationLaw (graphRawLaw F) K) A).toReal) :
    ∃ G : fermionGraph N, ∃ t ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ ht : 0 ≤ t,
      ‖fermionGraphValue N G‖^2 = 1 ∧
      graphRawLaw G = (ENNReal.ofReal (((physicalObservationLaw (graphRawLaw F) K) A).toReal))⁻¹ •
        Measure.map Prod.fst ((physicalObservationLaw (graphRawLaw F) K).restrict A) ∧
      radialPatchGapMean (graphFormVector G) y ht hb Z lam ≤
        dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ+
        sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y) ∧
      |Z/‖y‖-lam-(((physicalObservationLaw (graphRawLaw F) K) A).toReal)⁻¹*
        (∫ z in A, tfPotential (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r k) j c₁ r₀ s canonicalRealPacket
          (originalDatum (fun k : Fin K => dyadicObservationWidth r k) j z)) y
            ∂physicalObservationLaw (graphRawLaw F) K)-
        expectedRadialPatchCenter (graphFormVector G) y ht hb Z lam| ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) q+
        sharpLocalPotentialBudget (localCellRadius y)
          (localOffsetMass (dyadicUniformEventBudget ((2:ℝ)^j.val*r) (p₀ j) δ) y)
          (2*masterWidth c₁ r₀ s y) := by
  sorry

end

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior
attribute [local irreducible] dyadicUniformEventBudget sharpPatchRemainder sharpPotentialRemainder sharpLocalPotentialBudget

end CoulombAtom
end

end OAI
end
