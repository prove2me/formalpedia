-- Prove2me | Theorems.Thm_OAI_CoulombAtom_exists_own_state_exterior_number
-- name    : OAI.CoulombAtom.exists_own_state_exterior_number
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:30:42.640858+00:00
-- url     : https://prove2.me/theorems/f715e6ce-061c-4419-bbc1-ebfe350cf2ab
-- title:
--   OAI.CoulombAtom.exists_own_state_exterior_number: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.exists_own_state_exterior_number` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/ExteriorScreenNumerics.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ExteriorScreenNumerics.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped BigOperators InnerProductSpace`, `open CoulombBarrier`):
--
--   ```lean
--   lemma exists_own_state_exterior_number {Z s r : ℝ} {N : ℕ}
--       (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
--       (hN : PriceMinimizes (energy Z) (1/s^4) N)
--       (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
--       ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
--         (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.graphRawLaw` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.OwnProbabilityTailTiltState`, `OAI.CoulombAtom.actualScreenConstant`, `OAI.CoulombAtom.actualScreenRadius` and `OAI.CoulombAtom.rawExteriorCount` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombBarrier.exists_actual_selected_data_constants` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/ExteriorScreenNumerics.lean (declaration OAI.CoulombAtom.exists_own_state_exterior_number)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C010

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
open CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  fermionGraphValue formEnergy energy sectorExcessOperator graphRawLaw

lemma exists_own_state_exterior_number {Z s r : ℝ} {N : ℕ}
    (hZ : 0 ≤ Z) (hs : 0 < s) (hs1 : s ≤ 1) (hRs : actualScreenRadius*s ≤ 1) (hr : 0 < r)
    (hN : PriceMinimizes (energy Z) (1/s^4) N)
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) (h₀ : ∀ j, 0 < p₀ j) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z (1/s^4) r K p₀ 1 F ∧
      (∫ x, rawExteriorCount (2*(actualScreenRadius*s)) x ∂graphRawLaw F) ≤ actualScreenConstant/s := by
  sorry
end CoulombAtom

open MeasureTheory Filter Set Metric
open scoped Topology

end

end OAI
end
