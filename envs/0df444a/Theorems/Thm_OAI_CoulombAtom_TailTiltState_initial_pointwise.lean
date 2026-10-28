-- Prove2me | Theorems.Thm_OAI_CoulombAtom_TailTiltState_initial_pointwise
-- name    : OAI.CoulombAtom.TailTiltState.initial_pointwise
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:41:05.73341+00:00
-- url     : https://prove2.me/theorems/85789136-b424-463f-a0f9-fb66180bf76a
-- title:
--   OAI.CoulombAtom.TailTiltState.initial_pointwise: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.TailTiltState.initial_pointwise` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped BigOperators ENNReal ContDiff`, `open CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem TailTiltState.initial_pointwise {Z : ℕ} (hZ : 1 ≤ Z)
--       {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
--       (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) {N K : ℕ}
--       (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ θ : ℝ}
--       {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
--       (j : Fin (K+1)) (h₀ : 0 < p₀ j)
--       (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
--       (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
--         (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < θ)
--       {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
--       (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
--       (y : Space) (hy : ‖y‖ ≤ (11/10)*r₀) :
--       ((physicalObservationLaw (graphRawLaw F) K)
--         {z | θ < innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
--           (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
--             (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y}).toReal < p₀ j
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.IsRadial`, `OAI.CoulombAtom.SectorGraph`, `OAI.CoulombAtom.WeakGraphAmbient`, `OAI.CoulombAtom.fermionGraph`, `OAI.CoulombAtom.sectorDirections` and `OAI.CoulombAtom.weakGraph` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.PriceMinimizes` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombObservation.dyadicObservationWidth` and `OAI.CoulombAtom.Pauli.globalDensityConstant` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.graphRawLaw` (definitions bundle `OAIQ071C003` of this split); `OAI.CoulombAtom.dyadicUniformEventBudget` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.jointMasterPosterior`, `OAI.CoulombAtom.originalDatum` and `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.graphRawLaw_finite` and `OAI.CoulombAtom.innerPotential` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.TailTiltState` (definitions bundle `OAIQ071C010` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.Space`, `OAI.CoulombAtom.Spins` and `OAI.CoulombAtom.energy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombBarrier.own_state_initial_barrier` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/TailInitialPointwiseBarrier.lean (declaration OAI.CoulombAtom.TailTiltState.initial_pointwise)

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
section Work_TailInitialPointwise_barrier_scope

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

namespace CoulombAtom
open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

theorem TailTiltState.initial_pointwise {Z : ℕ} (hZ : 1 ≤ Z)
    {lam r₀ s c₁ : ℝ} (hlam : 0 < lam) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) {N K : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) {p₀ : Fin (K+1) → ℝ} {δ θ : ℝ}
    {F : fermionGraph N} (hF : TailTiltState Z lam r₀ K p₀ δ F)
    (j : Fin (K+1)) (h₀ : 0 < p₀ j)
    (hbudget : 3*(Z:ℝ)*lam+dyadicUniformEventBudget ((2:ℝ)^j.val*r₀) (p₀ j) δ ≤ (Z:ℝ)^(7/3:ℝ))
    (hsmall : (Pauli.globalDensityConstant*((Z:ℝ)^(7/3:ℝ)+(Z:ℝ)^(7/3:ℝ)))^(3/5:ℝ)*
      (8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) < θ)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (y : Space) (hy : ‖y‖ ≤ (11/10)*r₀) :
    ((physicalObservationLaw (graphRawLaw F) K)
      {z | θ < innerPotential r₀ (jointMasterPosterior (graphRawLaw F)
        (fun k : Fin K => dyadicObservationWidth r₀ k) j c₁ r₀ s g
          (originalDatum (fun k : Fin K => dyadicObservationWidth r₀ k) j z)) y}).toReal < p₀ j := by
  sorry

end CoulombAtom

end Work_TailInitialPointwise_barrier_scope

open MeasureTheory Filter Set Metric
open scoped Topology ContDiff

end

end OAI
end
