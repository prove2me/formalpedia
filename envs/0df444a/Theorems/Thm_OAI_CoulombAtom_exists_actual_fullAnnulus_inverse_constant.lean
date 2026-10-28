-- Prove2me | Theorems.Thm_OAI_CoulombAtom_exists_actual_fullAnnulus_inverse_constant
-- name    : OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:29:57.960856+00:00
-- url     : https://prove2.me/theorems/3d02a666-18b3-45ef-ad05-576d55cad552
-- title:
--   OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/FullAnnulusBandCover.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/FullAnnulusBandCover.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter Set`, `open scoped Topology BigOperators`, `open CoulombAnalysis CoulombObservation CoulombBarrier`):
--
--   ```lean
--   theorem exists_actual_fullAnnulus_inverse_constant {B c₁ lo hi xi : ℝ}
--       (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
--       (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
--       ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
--         {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
--         0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
--         (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
--           OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
--             (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
--         ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
--           let u := (2:ℝ)^j.val*r₀ i
--           ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
--             MeasurableSet[observationInformation
--               (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
--             (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
--             ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
--               (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u → ∀ h ∈ Icc lo hi,
--                 (localTFResponse h < (localCellRadius y)^6*
--                     originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
--                   h-xi ≤ (localCellRadius y)^4*
--                     originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
--                 ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
--                     localTFResponse h →
--                   (localCellRadius y)^4*
--                     originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
--               (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
--                 (localCellRadius y)^4*
--                   originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
--                     16*(tfPatchCapConstant+3))
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.localTFResponse`, `OAI.CoulombAtom.tinyProbabilityFloor` and `OAI.CoulombObservation.dyadicObservationWidth` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAnalysis.tfPatchCapConstant`, `OAI.CoulombAtom.graphRawLaw` and `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.observationInformation` and `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.OwnProbabilityTailTiltState`, `OAI.CoulombAtom.originalQueryDensity` and `OAI.CoulombAtom.originalQueryField` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually` and `OAI.CoulombBarrier.exists_actual_selected_data_constants` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/FullAnnulusBandCover.lean (declaration OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant)

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
open scoped Topology BigOperators
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue
attribute [local irreducible] physicalObservationLaw jointMasterPosterior

theorem exists_actual_fullAnnulus_inverse_constant {B c₁ lo hi xi : ℝ}
    (hB : 1 ≤ B) (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹)
    (hlh : lo ≤ hi) (hxi : 0 < xi) (hlo : 16*xi < lo) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} {l : Filter ι}
      {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ} {F : ∀ i, fermionGraph (N i)} {δ : ℝ},
      0 ≤ δ → Tendsto s l (𝓝 0) → (∀ᶠ i in l, 0 < r₀ i) →
      (∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
        OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
          (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) →
      ∀ᶠ i in l, ∀ j : Fin (K i), (2:ℝ)^j.val*r₀ i ≤ s i →
        let u := (2:ℝ)^j.val*r₀ i
        ∃ E : Set (Configuration (N i) × (Fin (K i) × (Fin (N i) × Fin 3) → ℝ)),
          MeasurableSet[observationInformation
            (fun k : Fin (K i) => dyadicObservationWidth (r₀ i) k) j] E ∧
          (physicalObservationLaw (graphRawLaw (F i)) (K i)).real E ≤ C*u^37 ∧
          ∀ᵐ q ∂physicalObservationLaw (graphRawLaw (F i)) (K i), q ∉ E →
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u → ∀ h ∈ Icc lo hi,
              (localTFResponse h < (localCellRadius y)^6*
                  originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y →
                h-xi ≤ (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y) ∧
              ((localCellRadius y)^6*originalQueryDensity (F i) (r₀ i) j c₁ (r₀ i) (s i) q y <
                  localTFResponse h →
                (localCellRadius y)^4*
                  originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤ h+xi)) ∧
            (∀ y : Space, u ≤ ‖y‖ → ‖y‖ ≤ B*u →
              (localCellRadius y)^4*
                originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) q y ≤
                  16*(tfPatchCapConstant+3)) := by
  sorry

end CoulombAtom

end

end OAI
end
