-- Prove2me | Theorems.Thm_OAI_JointDickman_centered_bin_spectral_jd
-- name    : OAI.JointDickman.centered_bin_spectral_jd
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-31T20:23:10.633253+00:00
-- url     : https://prove2.me/theorems/141b172c-8897-4ea5-82b9-557f5e1cfe78
-- title:
--   OAI.JointDickman.centered_bin_spectral_jd: intermediate lemma from OpenAI, The joint Dickman law for consecutive integers
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.JointDickmanPaper.joint_law`, `OAI.JointDickmanPaper.increasing_order` and `OAI.JointDickmanPaper.decreasing_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The joint Dickman law for consecutive integers*, OpenAI Math Release, September 24, 2026, result family 12, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.JointDickman.centered_bin_spectral` of [lean/OAI/NumberTheory/JointDickman/Amplification/CenteredBinSpectral.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/CenteredBinSpectral.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.JointDickman`, with `open Finset Filter MeasureTheory`, `open scoped Classical Topology`):
--
--   ```lean
--   theorem centered_bin_spectral_jd {J : ℕ} (hJ : 0<J)
--       (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
--       (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0)) :
--       ∃ C : ℝ, 0<C ∧ ∀ᶠ H : ℝ in atTop,
--       ∀ (E : Finset ℕ), (∀ p∈E, p.Prime) → ∀ w : ℕ → ℝ,
--       (∀ p∈E, 0≤w p ∧ w p≤1) → ∀ A : ℝ, 0<A →
--       ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, (A/2)*x≤N → (N:ℝ)≤(2*A)*x →
--       ∀ T : ℝ, 1≤T →
--         (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
--           (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤
--           17/H+4*canonicalAffineBase C H+(4*canonicalAffineSlope C H+128*Real.exp 1)*T/N
--   ```
--
--   **Definitions.** The statement is written with `OAI.JointDickman.angularMellinPolynomial`, `OAI.JointDickman.canonicalAffineBase`, `OAI.JointDickman.canonicalAffineSlope`, `OAI.JointDickman.centeredBinPrefix` and `OAI.JointDickman.centeredWeightedBinCoefficient` (definitions bundle `OAIQ083J001` of this split).
--
--   **Used by.** The proof of `OAI.JointDickman.coarse_residue_smoothing_energy_proved_jd` of this split imports it.
-- source:
--   OpenAI, The joint Dickman law for consecutive integers, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 12; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/JointDickman/Amplification/CenteredBinSpectral.lean (declaration OAI.JointDickman.centered_bin_spectral)

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_OAIQ083J001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace JointDickman
open Finset Filter MeasureTheory
open scoped Classical Topology

theorem centered_bin_spectral_jd {J : ℕ} (hJ : 0<J)
    (ζ : Fin (J-1) → ℂ) (hζ : ∀ i, ‖ζ i‖≤1) (μ : ℂ) (hμ : ‖μ‖≤1)
    (hmean : ∀ D : ℝ, 0<D → Tendsto (centeredBinPrefix J ζ μ D) atTop (𝓝 0)) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ H : ℝ in atTop,
    ∀ (E : Finset ℕ), (∀ p∈E, p.Prime) → ∀ w : ℕ → ℝ,
    (∀ p∈E, 0≤w p ∧ w p≤1) → ∀ A : ℝ, 0<A →
    ∀ᶠ x : ℝ in atTop, ∀ N : ℕ, (A/2)*x≤N → (N:ℝ)≤(2*A)*x →
    ∀ T : ℝ, 1≤T →
      (∫ t in -T..T, ‖angularMellinPolynomial (Ioc N (2*N))
        (centeredWeightedBinCoefficient J ζ μ E w x) t‖^2) ≤
        17/H+4*canonicalAffineBase C H+(4*canonicalAffineSlope C H+128*Real.exp 1)*T/N := by
  sorry

end JointDickman

end OAI
end
