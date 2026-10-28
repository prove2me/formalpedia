-- Prove2me | Theorems.Thm_OAI_CoulombAtom_exists_actual_own_probability_tail_tilt_state
-- name    : OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:35:29.230262+00:00
-- url     : https://prove2.me/theorems/d407f3d7-2850-401e-b93e-0dc0770aea48
-- title:
--   OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/OwnProbabilityTailTiltBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/OwnProbabilityTailTiltBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set`, `open scoped BigOperators ENNReal`, `open CoulombObservation`):
--
--   ```lean
--   theorem exists_actual_own_probability_tail_tilt_state {Z lam r : ℝ}
--       (hZ : 0 ≤ Z) (hr : 0 < r) {N : ℕ} (hN : PriceMinimizes (energy Z) lam N)
--       (K : ℕ) (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j) (hδ : 0 < δ) :
--       ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z lam r K p₀ δ F
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.OwnProbabilityTailTiltState` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombAtom.exists_own_state_exterior_number`, `OAI.CoulombAtom.exists_own_state_shell_residual` and `OAI.CoulombBarrier.exists_actual_selected_data_constants` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/OwnProbabilityTailTiltBarrier.lean (declaration OAI.CoulombAtom.exists_actual_own_probability_tail_tilt_state)

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

open MeasureTheory Filter Set
open scoped BigOperators ENNReal

namespace CoulombAtom
open CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem exists_actual_own_probability_tail_tilt_state {Z lam r : ℝ}
    (hZ : 0 ≤ Z) (hr : 0 < r) {N : ℕ} (hN : PriceMinimizes (energy Z) lam N)
    (K : ℕ) (p₀ : Fin (K+1) → ℝ) {δ : ℝ} (h₀ : ∀ j, 0 < p₀ j) (hδ : 0 < δ) :
    ∃ F : fermionGraph N, OwnProbabilityTailTiltState Z lam r K p₀ δ F := by
  sorry

end CoulombAtom

end

end OAI
end
