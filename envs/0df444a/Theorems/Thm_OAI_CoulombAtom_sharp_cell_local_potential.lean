-- Prove2me | Theorems.Thm_OAI_CoulombAtom_sharp_cell_local_potential
-- name    : OAI.CoulombAtom.sharp_cell_local_potential
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:38:08.543518+00:00
-- url     : https://prove2.me/theorems/26a51951-4ea8-4242-baf5-77f80571ff4a
-- title:
--   OAI.CoulombAtom.sharp_cell_local_potential: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.sharp_cell_local_potential` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/SharpLocalPotentialBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SharpLocalPotentialBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped Topology`):
--
--   ```lean
--    theorem sharp_cell_local_potential {N : ℕ} {ψ : FormVector N}
--       (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
--       (ha1 : localCellRadius y ≤ 1) {Z lam q : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
--       (hq : 0 < q) (hqR : q ≤ 4*localCellRadius y) :
--       (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
--         (sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y)^(3/5:ℝ)*
--           (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.corePriceExcess` and `OAI.CoulombAtom.formRawLaw` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.localOffsetMass` and `OAI.CoulombAtom.rawLocalPotential` (definitions bundle `OAIQ071C007` of this split); `OAI.CoulombAtom.sharpOrdinaryDensityConstant` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.FormAdmissible`, `OAI.CoulombAtom.FormVector` and `OAI.CoulombAtom.Space` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombAtom.OwnProbabilityTailTiltState.expandedAnnulus_small_event_integral`, `OAI.CoulombAtom.OwnProbabilityTailTiltState.rare_cap_event_of_cell`, `OAI.CoulombAtom.TailTiltState.event_radial_comparison_of_cell`, `OAI.CoulombAtom.sharp_joint_selected_patch` and `OAI_CoulombAtom_sharp_selected_potential_error` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SharpLocalPotentialBarrier.lean (declaration OAI.CoulombAtom.sharp_cell_local_potential)

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

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
section Work_SharpLocalPotential_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology

 theorem sharp_cell_local_potential {N : ℕ} {ψ : FormVector N}
    (hψ : FormAdmissible ψ) {y : Space} (hy : y ≠ 0)
    (ha1 : localCellRadius y ≤ 1) {Z lam q : ℝ} (hZ : 0 ≤ Z) (hlam : 0 < lam)
    (hq : 0 < q) (hqR : q ≤ 4*localCellRadius y) :
    (∫ x, rawLocalPotential y q x ∂formRawLaw ψ) ≤
      (sharpOrdinaryDensityConstant*(localOffsetMass (max (corePriceExcess Z lam ψ) 0) y)^2/localCellRadius y)^(3/5:ℝ)*
        (8*Real.pi)^(2/5:ℝ)*q^(1/5:ℝ) := by
  sorry

end Work_SharpLocalPotential_barrier_scope

open MeasureTheory Set Metric
open scoped BigOperators

open CoulombAnalysis CoulombNeumann

end CoulombAtom

end

end OAI
end
