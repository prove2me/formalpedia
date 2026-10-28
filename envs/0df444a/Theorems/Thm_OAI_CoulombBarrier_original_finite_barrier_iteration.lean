-- Prove2me | Theorems.Thm_OAI_CoulombBarrier_original_finite_barrier_iteration
-- name    : OAI.CoulombBarrier.original_finite_barrier_iteration
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:23:40.048187+00:00
-- url     : https://prove2.me/theorems/37d7cfd7-42f1-4143-af39-028d66ce2751
-- title:
--   OAI.CoulombBarrier.original_finite_barrier_iteration: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombBarrier.original_finite_barrier_iteration` of [lean/OAI/Analysis/CoulombIonization/RadialBounds/BarrierActualInitializationBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/BarrierActualInitializationBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombBarrier`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped Topology BigOperators`, `open CoulombAtom CoulombAnalysis CoulombObservation`):
--
--   ```lean
--   theorem original_finite_barrier_iteration {N K J : ℕ} (μ : Measure (Configuration N))
--       [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {c₁ r₀ s : ℝ}
--       (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
--       {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
--       (hgn : ∫ z, (g z)^2 = 1)
--       {Z κ B C M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
--       (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh)
--       (hA : 0 ≤ A) (hQ : 0 ≤ Q)
--       (good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
--       [∀ j, DecidablePred (good j)] (hgood : ∀ j < J, MeasurableSet {sample | good j sample})
--       {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
--       (initial : IsNuclearBarrier (physicalObservationLaw μ K)
--         (originalMasterField μ ell 0 c₁ r₀ s g) Z κ B C r₀ T η a p)
--       (hcap : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
--         nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
--       (hinv : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
--         InverseComparisonAt ‖x‖
--           (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
--           (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
--       (hprob : ∀ j < J, (physicalObservationLaw μ K).real {sample | ¬good j sample} ≤ A*((2:ℝ)^j*r₀)^25)
--       (hmoment : ∀ j < J, ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 2*((2:ℝ)^j*r₀) →
--         (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
--           Q*((2:ℝ)^j*r₀)^(-12-6*masterExponent)) :
--       ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
--         (originalMasterField μ ell J c₁ r₀ s g) Z κ B C ((2:ℝ)^J*r₀) (max T M)
--         (η+∑ j ∈ Finset.range J, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
--           ((2:ℝ)^j*r₀)^barrierErrorExponent) a' p'
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.TFSpace` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.masterExponent` (definitions bundle `OAIQ071C001` of this split); `OAI.CoulombBarrier.InverseComparisonAt` and `OAI.CoulombBarrier.OutwardCalibration` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombBarrier.IsNuclearBarrier`, `OAI.CoulombBarrier.barrierErrorExponent`, `OAI.CoulombBarrier.meanFieldOffset` and `OAI.CoulombBarrier.nuclearField` (definitions bundle `OAIQ071C005` of this split); `OAI.CoulombAtom.physicalObservationLaw` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombBarrier.originalMasterField` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.Configuration` and `OAI.CoulombAtom.Space` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proof of `OAI.CoulombBarrier.actual_outward_barrier_given_state_eventually` of this split imports it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/RadialBounds/BarrierActualInitializationBarrier.lean (declaration OAI.CoulombBarrier.original_finite_barrier_iteration)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C009

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombBarrier

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped Topology BigOperators

open CoulombAtom CoulombAnalysis CoulombObservation
attribute [local instance] physicalObservationLaw_probability

theorem original_finite_barrier_iteration {N K J : ℕ} (μ : Measure (Configuration N))
    [IsProbabilityMeasure μ] (ell : Fin K → ℝ) {c₁ r₀ s : ℝ}
    (hc : 0 < c₁) (hr₀ : 0 < r₀) (hs : 0 < s) (hrs : r₀ ≤ s)
    {g : Space → ℝ} (hg : Continuous g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1)
    {Z κ B C M lam1 lam2 e ξ Cinv hl hh T η A Q lam : ℝ}
    (cal : OutwardCalibration κ B C M lam1 lam2 e ξ hl hh)
    (hA : 0 ≤ A) (hQ : 0 ≤ Q)
    (good : ℕ → (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → Prop)
    [∀ j, DecidablePred (good j)] (hgood : ∀ j < J, MeasurableSet {sample | good j sample})
    {a p : (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ)) → TFSpace → ℝ}
    (initial : IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell 0 c₁ r₀ s g) Z κ B C r₀ T η a p)
    (hcap : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x ≤ C/‖x‖^4)
    (hinv : ∀ j < J, ∀ sample, good j sample → ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 4*M*((2:ℝ)^j*r₀) →
      InverseComparisonAt ‖x‖
        (nuclearField Z x+meanFieldOffset lam (originalMasterField μ ell j c₁ r₀ s g sample) x)
        (originalMasterField μ ell j c₁ r₀ s g sample x) κ hl hh ξ Cinv)
    (hprob : ∀ j < J, (physicalObservationLaw μ K).real {sample | ¬good j sample} ≤ A*((2:ℝ)^j*r₀)^25)
    (hmoment : ∀ j < J, ∀ x, (2:ℝ)^j*r₀ ≤ ‖x‖ → ‖x‖ < 2*((2:ℝ)^j*r₀) →
      (∫ sample, (originalMasterField μ ell j c₁ r₀ s g sample x)^2 ∂physicalObservationLaw μ K) ≤
        Q*((2:ℝ)^j*r₀)^(-12-6*masterExponent)) :
    ∃ a' p', IsNuclearBarrier (physicalObservationLaw μ K)
      (originalMasterField μ ell J c₁ r₀ s g) Z κ B C ((2:ℝ)^J*r₀) (max T M)
      (η+∑ j ∈ Finset.range J, (32*Real.pi/3*Real.sqrt A*Real.sqrt Q)*
        ((2:ℝ)^j*r₀)^barrierErrorExponent) a' p' := by
  sorry

end CoulombBarrier

end

end OAI
end
