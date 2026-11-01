-- Prove2me | Theorems.Thm_OAI_JointDickman_twisted_bin_spectral_jd
-- name    : OAI.JointDickman.twisted_bin_spectral_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:35:35.127284+00:00
-- url     : https://prove2.me/theorems/cb6f0139-0134-47fd-9882-4fe119cdbfa6
-- title:
--   OAI.JointDickman.twisted_bin_spectral_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.twisted_bin_spectral` of [lean/OAI/NumberTheory/JointDickman/Amplification/TwistedBinSpectral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/TwistedBinSpectral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory TwoPointCorrelations`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem twisted_bin_spectral_jd
--       {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
--       : ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
--         ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) →
--         ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
--         ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
--         ∀ x : ℝ, (N:ℝ)/A ≤ x → ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
--         (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) → ∀ T : ℝ, 1 ≤ T →
--         (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
--           (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
--             (finitePrimeWeight E w) a χ) t‖^2) ≤
--           4/H+canonicalAffineBase C H+(canonicalAffineSlope C H+32*Real.exp 1)*T/N
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.angularMellinPolynomial`, `OAI.JointDickman.canonicalAffineBase`, `OAI.JointDickman.canonicalAffineSlope`, `OAI.JointDickman.finitePrimeWeight` and `OAI.JointDickman.primeBin` (definitions bundle `OAIQ083J001` of this split); `OAI.JointDickman.twistedWeightedBinInterpolant` (definitions bundle `OAIQ083J003` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/TwistedBinSpectral.lean (declaration OAI.JointDickman.twisted_bin_spectral)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J003

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory TwoPointCorrelations
open scoped Classical Topology

theorem twisted_bin_spectral_jd
    {ι : Type*} [Fintype ι] {J : ℕ} (hJ : 0 < J) (j : ι → ℕ) (hj : ∀ i, 1 ≤ j i)
    : ∃ C : ℝ, 0 < C ∧ ∀ᶠ H : ℝ in atTop,
      ∀ (E : Finset ℕ), (∀ p ∈ E, p.Prime) →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ A : ℝ, 0 < A → ∀ᶠ N : ℕ in atTop,
      ∀ x : ℝ, (N:ℝ)/A ≤ x → ∀ (m : ℕ) (a : ι → Fin m) (w : ℕ → ℝ),
      (∀ p ∈ E, 0 ≤ w p ∧ w p ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
        (twistedWeightedBinInterpolant (fun i => primeBin x J (j i))
          (finitePrimeWeight E w) a χ) t‖^2) ≤
        4/H+canonicalAffineBase C H+(canonicalAffineSlope C H+32*Real.exp 1)*T/N := by
  sorry

end JointDickman

end OAI
end
