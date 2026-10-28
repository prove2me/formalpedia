-- Prove2me | Theorems.Thm_OAI_CoulombAtom_actual_scaled_original_cap_eventually
-- name    : OAI.CoulombAtom.actual_scaled_original_cap_eventually
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:29:09.786922+00:00
-- url     : https://prove2.me/theorems/507c0faf-8feb-40f3-ab5e-e18f36696f7f
-- title:
--   OAI.CoulombAtom.actual_scaled_original_cap_eventually: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.actual_scaled_original_cap_eventually` of [lean/OAI/Analysis/CoulombIonization/Variational/ScaledOriginalCap.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/ScaledOriginalCap.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter Set`, `open scoped Topology`, `open CoulombAnalysis CoulombObservation CoulombBarrier`):
--
--   ```lean
--    theorem actual_scaled_original_cap_eventually {ι : Type*} {l : Filter ι}
--       {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
--       {F : ∀ i, fermionGraph (N i)} {a c₁ δ : ℝ} (ha : 1/2 ≤ a)
--       (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
--       (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
--       (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
--         OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
--           (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
--       ∀ᶠ i in l, ∀ j : Fin (K i+1), (2:ℝ)^j.val*r₀ i ≤ s i →
--         let u := (2:ℝ)^j.val*r₀ i
--         let T := fun z => capBandStatistic (a*u) (tfPatchCapConstant+2)
--           (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
--         Measurable T ∧
--         (physicalObservationLaw (graphRawLaw (F i)) (K i)).real {z | 1 < T z} ≤
--           4096*(tfPatchCapConstant+2)*u^60 ∧
--         ∀ z, T z ≤ 1 → ∀ y, 5*(a*u)/4 ≤ ‖y‖ → ‖y‖ ≤ 7*(a*u)/4 →
--           (localCellRadius y)^4*
--             originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y ≤
--             16*(tfPatchCapConstant+3)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.tinyProbabilityFloor` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAnalysis.tfPatchCapConstant`, `OAI.CoulombAtom.graphRawLaw` and `OAI.CoulombAtom.localCellRadius` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.capBandStatistic` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.OwnProbabilityTailTiltState` and `OAI.CoulombAtom.originalQueryField` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.Spins` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI.CoulombAtom.exists_actual_fullAnnulus_inverse_constant` and `OAI_CoulombAtom_exists_actual_scaled_original_regularity_constants` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Variational/ScaledOriginalCap.lean (declaration OAI.CoulombAtom.actual_scaled_original_cap_eventually)

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

 theorem actual_scaled_original_cap_eventually {ι : Type*} {l : Filter ι}
    {r₀ s Z lam : ι → ℝ} {N K : ι → ℕ}
    {F : ∀ i, fermionGraph (N i)} {a c₁ δ : ℝ} (ha : 1/2 ≤ a)
    (hc : 0 < c₁) (hcL : c₁ < (10*(100000:ℝ))⁻¹) (hδ : 0 ≤ δ)
    (hs0 : Tendsto s l (𝓝 0)) (hr₀ : ∀ᶠ i in l, 0 < r₀ i)
    (hstate : ∀ᶠ i in l, 0 ≤ Z i ∧ 0 < lam i ∧
      OwnProbabilityTailTiltState (Z i) (lam i) (r₀ i) (K i)
        (fun k => tinyProbabilityFloor (Z i) ((2:ℝ)^k.val*r₀ i)) δ (F i)) :
    ∀ᶠ i in l, ∀ j : Fin (K i+1), (2:ℝ)^j.val*r₀ i ≤ s i →
      let u := (2:ℝ)^j.val*r₀ i
      let T := fun z => capBandStatistic (a*u) (tfPatchCapConstant+2)
        (originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z)
      Measurable T ∧
      (physicalObservationLaw (graphRawLaw (F i)) (K i)).real {z | 1 < T z} ≤
        4096*(tfPatchCapConstant+2)*u^60 ∧
      ∀ z, T z ≤ 1 → ∀ y, 5*(a*u)/4 ≤ ‖y‖ → ‖y‖ ≤ 7*(a*u)/4 →
        (localCellRadius y)^4*
          originalQueryField (F i) (Z i) (lam i) (r₀ i) j c₁ (r₀ i) (s i) z y ≤
          16*(tfPatchCapConstant+3) := by
  sorry

open MeasureTheory Filter Set
open scoped Topology
open CoulombAnalysis CoulombObservation CoulombBarrier
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end
