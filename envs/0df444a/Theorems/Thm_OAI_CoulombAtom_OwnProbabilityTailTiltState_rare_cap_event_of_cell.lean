-- Prove2me | Theorems.Thm_OAI_CoulombAtom_OwnProbabilityTailTiltState_rare_cap_event_of_cell
-- name    : OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:24:59.900494+00:00
-- url     : https://prove2.me/theorems/852cc7a3-26fc-49b8-9189-655ea438118f
-- title:
--   OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/PointInverseEventsCell.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/PointInverseEventsCell.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter Set`, `open scoped Topology`, `open CoulombAnalysis CoulombObservation CoulombBarrier`):
--
--   ```lean
--   theorem OwnProbabilityTailTiltState.rare_cap_event_of_cell {Z lam r : ℝ}
--       (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
--       {δ c₁ r₀ s : ℝ}
--       (hF : OwnProbabilityTailTiltState Z lam r K
--         (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
--       (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
--       (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
--       (j : Fin (K+1)) {y : Space} (hy : y ≠ 0)
--       (hu1 : (2:ℝ)^j.val*r ≤ 1)
--       (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
--       (hcap : originalFieldCapBudget ((2:ℝ)^j.val*r) (((2:ℝ)^j.val*r)^80) δ c₁ r₀ s y
--           ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent) <
--           (tfPatchCapConstant+2)/(localCellRadius y)^4) :
--       (physicalObservationLaw (graphRawLaw F) K).real
--         {z | (tfPatchCapConstant+2)/(localCellRadius y)^4 <
--           originalQueryField F Z lam r j c₁ r₀ s z y} < ((2:ℝ)^j.val*r)^80
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.masterExponent` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.tinyProbabilityFloor` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAnalysis.tfPatchCapConstant`, `OAI.CoulombAtom.graphRawLaw` and `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.InverseFiniteGeometry`, `OAI.CoulombAtom.OwnProbabilityTailTiltState`, `OAI.CoulombAtom.originalFieldCapBudget` and `OAI.CoulombAtom.originalQueryField` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombAtom_actual_expandedAnnulus_cap_excess_uniform_eventually` and `OAI.CoulombAtom.actual_scaled_original_cap_eventually` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/PointInverseEventsCell.lean (declaration OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell)

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

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem OwnProbabilityTailTiltState.rare_cap_event_of_cell {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hr : 0 < r) {N K : ℕ} {F : fermionGraph N}
    {δ c₁ r₀ s : ℝ}
    (hF : OwnProbabilityTailTiltState Z lam r K
      (fun j => tinyProbabilityFloor Z ((2:ℝ)^j.val*r)) δ F)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hr₀ : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (j : Fin (K+1)) {y : Space} (hy : y ≠ 0)
    (hu1 : (2:ℝ)^j.val*r ≤ 1)
    (hgeom : InverseFiniteGeometry c₁ r₀ s (((2:ℝ)^j.val*r)^(101/100:ℝ)) y)
    (hcap : originalFieldCapBudget ((2:ℝ)^j.val*r) (((2:ℝ)^j.val*r)^80) δ c₁ r₀ s y
        ((localCellRadius y)^(6/5:ℝ)) (localCellRadius y*(localCellRadius y)^masterExponent) <
        (tfPatchCapConstant+2)/(localCellRadius y)^4) :
    (physicalObservationLaw (graphRawLaw F) K).real
      {z | (tfPatchCapConstant+2)/(localCellRadius y)^4 <
        originalQueryField F Z lam r j c₁ r₀ s z y} < ((2:ℝ)^j.val*r)^80 := by
  sorry

end CoulombAtom

end

end OAI
end
