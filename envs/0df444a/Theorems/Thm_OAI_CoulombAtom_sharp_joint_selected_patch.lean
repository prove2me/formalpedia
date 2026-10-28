-- Prove2me | Theorems.Thm_OAI_CoulombAtom_sharp_joint_selected_patch
-- name    : OAI.CoulombAtom.sharp_joint_selected_patch
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:36:15.04036+00:00
-- url     : https://prove2.me/theorems/2fc78fd0-069b-4177-96a4-ee0293e274b8
-- title:
--   OAI.CoulombAtom.sharp_joint_selected_patch: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.sharp_joint_selected_patch` of [lean/OAI/Analysis/CoulombIonization/Ionization/SharpJointComparisonBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SharpJointComparisonBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Set Metric`, `open scoped BigOperators ENNReal ContDiff`, `open CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem sharp_joint_selected_patch {N : ℕ} {ψ : FormVector N}
--       (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
--       {b Z lam q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
--       (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
--       (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
--       (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
--       ∃ r ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ hr0 : 0 ≤ r,
--         radialPatchGapMean ψ y hr0 hb Z lam ≤ corePriceExcess Z lam ψ+
--           sharpPatchRemainder (localCellRadius y) b
--             (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) ∧
--         radialPotentialError ψ y hr0 hb Z lam q ≤
--           sharpPotentialRemainder (localCellRadius y) b
--             (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
--             (max (corePriceExcess Z lam ψ) 0) q
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.corePriceExcess` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.localOffsetMass` (definitions bundle `OAIQ071C007` of this split); `OAI.CoulombAtom.radialPatchGapMean` (definitions bundle `OAIQ071C008` of this split); `OAI.CoulombAtom.radialPotentialError`, `OAI.CoulombAtom.sharpPatchRemainder` and `OAI.CoulombAtom.sharpPotentialRemainder` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.FormAdmissible`, `OAI.CoulombAtom.FormVector` and `OAI.CoulombAtom.Space` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombAtom.OwnProbabilityTailTiltState.expandedAnnulus_small_event_integral`, `OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell`, `OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell` and `OAI.CoulombAtom.actual_uniform_upper_deficit` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/SharpJointComparisonBarrier.lean (declaration OAI.CoulombAtom.sharp_joint_selected_patch)

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

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation

theorem sharp_joint_selected_patch {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0) (ha1 : localCellRadius y ≤ 1)
    {b Z lam q : ℝ} (hb : 0 < b) (hba : 2*b ≤ localCellRadius y)
    (hZ : 0 ≤ Z) (hlam : 0 < lam) (hq : 0 < q)
    (hqr : q+Real.sqrt 3*b ≤ 4*localCellRadius y)
    (hcollar : localCellRadius y ≤ b^2*localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) :
    ∃ r ∈ Icc (5*localCellRadius y) (6*localCellRadius y), ∃ hr0 : 0 ≤ r,
      radialPatchGapMean ψ y hr0 hb Z lam ≤ corePriceExcess Z lam ψ+
        sharpPatchRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y) ∧
      radialPotentialError ψ y hr0 hb Z lam q ≤
        sharpPotentialRemainder (localCellRadius y) b
          (localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)
          (max (corePriceExcess Z lam ψ) 0) q := by
  sorry

end CoulombAtom

end

end OAI
end
