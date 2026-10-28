-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_tail_initial_good_event
-- name    : OAI.CoulombBarrier.tail_initial_good_event
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:36:57.228468+00:00
-- url     : https://prove2.me/theorems/a51c0eac-07e5-4bf4-b4e5-237b6ef9c7c1
-- title:
--   OAI.CoulombBarrier.tail_initial_good_event: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.tail_initial_good_event` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped BigOperators ContDiff`, `open CoulombAtom CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem tail_initial_good_event {Z : ℕ} (hZ : 1 ≤ Z)
--       {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
--       (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
--       {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
--       {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
--       (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
--       (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
--       (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
--         (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < (Z:ℝ)/(20*r₀))
--       (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
--       {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
--       (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
--       (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
--       ∃ A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
--         MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j] A ∧
--         (∀ z ∈ A, ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
--           innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
--             (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
--               (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y ≤ (Z:ℝ)/(10*r₀)) ∧
--         (physicalObservationLaw (graphRawLaw F) K).real Aᶜ ≤ 1728*r₀^37
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.IsRadial`, `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.PriceMinimizes` and `OAI.CoulombAtom.masterExponent` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombObservation.dyadicObservationWidth` and `OAI.CoulombAtom.Pauli.globalDensityConstant` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.graphRawLaw` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.dyadicUniformEventBudget` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.jointMasterPosterior`, `OAI.CoulombAtom.observationInformation`, `OAI.CoulombAtom.originalDatum` and `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.graphRawLaw_finite` and `OAI.CoulombAtom.innerPotential` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.TailTiltState` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean (declaration OAI.CoulombBarrier.tail_initial_good_event)

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

section Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ContDiff

namespace CoulombBarrier
open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem tail_initial_good_event {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hr1 : r₀ ≤ 1)
    (hs : 0 < s) (hs1 : s ≤ 1) (hrs : r₀ ≤ s) (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2)
    {N K : ℕ} (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ G : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j) (hp40 : p₀ j ≤ r₀^40)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < (Z:ℝ)/(20*r₀))
    (hinterp : (48*Real.pi*G*c₁⁻¹^3)*r₀^(1-3*masterExponent) ≤ 1/20)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hG : ∀ z, (g z)^2 ≤ G) (hgn : ∫ z, (g z)^2 = 1)
    (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1) :
    ∃ A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)),
      MeasurableSet[observationInformation (fun k : Fin K => dyadicObservationWidth r₀ k) j] A ∧
      (∀ z ∈ A, ∀ y : Space, ‖y‖ ≤ (11/10)*r₀ →
        innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
          (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
            (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y ≤ (Z:ℝ)/(10*r₀)) ∧
      (physicalObservationLaw (graphRawLaw F) K).real Aᶜ ≤ 1728*r₀^37 := by
  sorry

end CoulombBarrier

end Work_TailInitialGood_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

end

end OAI
end
