-- Prove2me | Theorems.Thm_OAI_JointDickman_auxiliary_power_energy_jd
-- name    : OAI.JointDickman.auxiliary_power_energy_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:22:36.095188+00:00
-- url     : https://prove2.me/theorems/d472a6a7-3199-4b02-b89d-7da658a5b32d
-- title:
--   OAI.JointDickman.auxiliary_power_energy_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.auxiliary_power_energy` of [lean/OAI/NumberTheory/JointDickman/Counting/AuxiliaryPowerEnergy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/AuxiliaryPowerEnergy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory TwoPointCorrelations`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem auxiliary_power_energy_jd (P₀ Q₀ H : ℝ)
--       (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
--       (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
--       (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hH : 2 ≤ H)
--       {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 1/12) :
--       ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
--         let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
--         let K := auxiliaryLogBins H α β N
--         let J := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
--         let B := canonicalMellinBands P₀ Q₀ (1/12)
--         ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
--         ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ N →
--         E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J →
--         (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (mrtPrimeLogLower H k) t‖ ≤ b) →
--         (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
--           ε+22528*Real.exp 1/H+D*b^2+
--           48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.MellinPrimeBands`, `OAI.JointDickman.angularMellinPolynomial`, `OAI.JointDickman.auxiliaryLogBins`, `OAI.JointDickman.canonicalMellinBands`, `OAI.JointDickman.mellinBandCount`, `OAI.TwoPointCorrelations.mrtBaseResolution`, `OAI.TwoPointCorrelations.mrtPrimeBand`, `OAI.TwoPointCorrelations.mrtPrimeLogLower` and `OAI.JointDickman.MellinPrimeBands.polynomial` (definitions bundle `OAIQ083J001` of this split); `OAI.TwoPointCorrelations.Multiplicative`, `OAI.TwoPointCorrelations.mrtCofactorPolynomial`, `OAI.TwoPointCorrelations.mrtNoSmallBand` and `OAI.TwoPointCorrelations.mrtPrimeAvoids` (definitions bundle `OAIQ083J002` of this split).
--
--   **Used by.** The proofs of `OAI.JointDickman.centered_bin_spectral_jd` and `OAI.JointDickman.twisted_bin_spectral_jd` of this split import it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Counting/AuxiliaryPowerEnergy.lean (declaration OAI.JointDickman.auxiliary_power_energy)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001
import Definitions.Def_OAIQ083J002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem auxiliary_power_energy_jd (P₀ Q₀ H : ℝ)
    (hP₀ : 2*Real.exp 1 ≤ P₀) (hPQ : P₀ ≤ Q₀)
    (hlogP : 1 ≤ Real.log P₀) (hQ₀ : 1 ≤ Real.log Q₀)
    (hH₀ : 2 ≤ mrtBaseResolution P₀ Q₀ (1/12)) (hH : 2 ≤ H)
    {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) (hβ : β < 1/12) :
    ∃ D : ℝ, 0 < D ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      let P := mrtPrimeBand ((N:ℝ)^α) ((N:ℝ)^β)
      let K := auxiliaryLogBins H α β N
      let J := mellinBandCount Q₀ (Real.sqrt (Real.log (N:ℝ))) hQ₀
      let B := canonicalMellinBands P₀ Q₀ (1/12)
      ∀ (F : ℕ → ℂ), Multiplicative F → (∀ n, ‖F n‖ ≤ 1) →
      ∀ (E : Set ℝ) (T b : ℝ), MeasurableSet E → 0 < T → T ≤ N →
      E ⊆ Set.Ioc (-T) T → E ⊆ mrtNoSmallBand B.bins (B.polynomial F) B.threshold J →
      (∀ k ∈ K, ∀ t ∈ E, ‖mrtCofactorPolynomial P F N (mrtPrimeLogLower H k) t‖ ≤ b) →
      (∫ t in E, ‖angularMellinPolynomial (Ioc N (2*N)) F t‖^2) ≤
        ε+22528*Real.exp 1/H+D*b^2+
        48*Real.exp 1*(((Ioc N (2*N)).filter (mrtPrimeAvoids P)).card:ℝ)/N := by
  sorry

end JointDickman

end OAI
end
