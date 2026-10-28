-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_exists_actual_selected_data_constants
-- name    : OAI.CoulombBarrier.exists_actual_selected_data_constants
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:37:15.425043+00:00
-- url     : https://prove2.me/theorems/4ef4997c-b33a-4c3a-bc10-f31c827a604b
-- title:
--   OAI.CoulombBarrier.exists_actual_selected_data_constants: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.exists_actual_selected_data_constants` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedData.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedData.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter Set Metric`, `open scoped Topology`, `open CoulombAtom CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem exists_actual_selected_data_constants :
--       ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧
--         ∀ {ι : Type*} {f : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N : ι → ℕ),
--           (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s f (𝓝 0) →
--           Tendsto (fun i => (Z i:ℝ)*(s i)^3) f atTop →
--           (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
--           ∀ l : ℝ, 1 ≤ l → ∀ᶠ i in f,
--             Nonempty (SelectedQuantumData (Z i) (N i) (s i) l (selectedTailThreshold (s i)) B C selectedTailRadius)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombBarrier.SelectedQuantumData`, `OAI.CoulombBarrier.selectedTailRadius` and `OAI.CoulombBarrier.selectedTailThreshold` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombAtom_actual_priced_deficit_limit` and `OAI.CoulombAtom.generalized_ionization` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectedData.lean (declaration OAI.CoulombBarrier.exists_actual_selected_data_constants)

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

namespace CoulombBarrier

section
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphRawLaw physicalObservationLaw jointMasterPosterior

theorem exists_actual_selected_data_constants :
    ∃ B C : ℝ, 0 < B ∧ 0 ≤ C ∧
      ∀ {ι : Type*} {f : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s f (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) f atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ l : ℝ, 1 ≤ l → ∀ᶠ i in f,
          Nonempty (SelectedQuantumData (Z i) (N i) (s i) l (selectedTailThreshold (s i)) B C selectedTailRadius) := by
  sorry

end
open MeasureTheory Filter Set Metric
open scoped Topology
open CoulombAtom CoulombAnalysis

end CoulombBarrier

end

end OAI
end
