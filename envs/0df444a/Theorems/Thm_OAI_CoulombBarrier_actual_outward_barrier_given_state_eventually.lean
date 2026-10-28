-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_actual_outward_barrier_given_state_eventually
-- name    : OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:33:18.325259+00:00
-- url     : https://prove2.me/theorems/2877a072-d7b6-46fb-b78a-e599717a2ecb
-- title:
--   OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectionBudget.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectionBudget.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter Set Metric`, `open scoped Topology BigOperators`, `open CoulombAtom CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem actual_outward_barrier_given_state_eventually {c : ℝ} (hc : 0 < c)
--       (hcL : c < (10*(100000:ℝ))⁻¹) :
--       ∃ ε B C M D : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧ 2 < M ∧ 0 ≤ D ∧
--         ∀ {ι : Type*} {l : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N K : ι → ℕ),
--           (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s l (𝓝 0) →
--           Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop →
--           (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
--           ∀ F : ∀ i, fermionGraph (N i),
--             (∀ i, OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (ε*(Z i:ℝ)^(-1/3:ℝ)) (K i)
--               (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*(ε*(Z i:ℝ)^(-1/3:ℝ)))) 1 (F i)) →
--             ∀ᶠ i in l, ∀ J : ℕ, J ≤ K i → (2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ)) ≤ s i →
--               ∃ a p : (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) → TFSpace → ℝ,
--                 IsNuclearBarrier (physicalObservationLaw (graphRawLaw (F i)) (K i))
--                   (originalQueryDensity (F i) (ε*(Z i:ℝ)^(-1/3:ℝ)) J c (ε*(Z i:ℝ)^(-1/3:ℝ)) (s i))
--                   (Z i:ℝ) tfDensityCoefficient B C ((2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ))) M
--                   (5184*(s i)^32+D*(s i)^barrierErrorExponent) a p
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.TFSpace`, `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAnalysis.tfDensityCoefficient` and `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombAtom.tinyProbabilityFloor` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.graphRawLaw` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombBarrier.IsNuclearBarrier` and `OAI.CoulombBarrier.barrierErrorExponent` (definitions bundle `OAIQ071C005` of this split); `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.OwnProbabilityTailTiltState` and `OAI.CoulombAtom.originalQueryDensity` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombBarrier.exists_actual_selected_data_constants` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/SelectionBudget.lean (declaration OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually)

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

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local instance] physicalObservationLaw_probability

theorem actual_outward_barrier_given_state_eventually {c : ℝ} (hc : 0 < c)
    (hcL : c < (10*(100000:ℝ))⁻¹) :
    ∃ ε B C M D : ℝ, 0 < ε ∧ ε < 1 ∧ 0 < B ∧ 2 < M ∧ 0 ≤ D ∧
      ∀ {ι : Type*} {l : Filter ι} (Z : ι → ℕ) (s : ι → ℝ) (N K : ι → ℕ),
        (∀ i, 1 ≤ Z i) → (∀ i, 0 < s i) → Tendsto s l (𝓝 0) →
        Tendsto (fun i => (Z i:ℝ)*(s i)^3) l atTop →
        (∀ i, PriceMinimizes (energy (Z i)) ((s i)^(-4:ℝ)) (N i)) →
        ∀ F : ∀ i, fermionGraph (N i),
          (∀ i, OwnProbabilityTailTiltState (Z i) ((s i)^(-4:ℝ)) (ε*(Z i:ℝ)^(-1/3:ℝ)) (K i)
            (fun j => tinyProbabilityFloor (Z i) ((2:ℝ)^j.val*(ε*(Z i:ℝ)^(-1/3:ℝ)))) 1 (F i)) →
          ∀ᶠ i in l, ∀ J : ℕ, J ≤ K i → (2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ)) ≤ s i →
            ∃ a p : (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)) → TFSpace → ℝ,
              IsNuclearBarrier (physicalObservationLaw (graphRawLaw (F i)) (K i))
                (originalQueryDensity (F i) (ε*(Z i:ℝ)^(-1/3:ℝ)) J c (ε*(Z i:ℝ)^(-1/3:ℝ)) (s i))
                (Z i:ℝ) tfDensityCoefficient B C ((2:ℝ)^J*(ε*(Z i:ℝ)^(-1/3:ℝ))) M
                (5184*(s i)^32+D*(s i)^barrierErrorExponent) a p := by
  sorry

end CoulombBarrier

end

end OAI
end
