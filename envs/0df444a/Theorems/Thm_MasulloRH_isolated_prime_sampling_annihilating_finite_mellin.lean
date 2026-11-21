-- Prove2me | Theorems.Thm_MasulloRH_isolated_prime_sampling_annihilating_finite_mellin
-- name    : MasulloRH.isolated_prime_sampling_annihilating_finite_mellin
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T02:35:11.450568+00:00
-- url     : https://prove2.me/theorems/bc8dbebf-c00d-4fc4-b3bf-3fdab153b75e
-- title:
--   Prime sampling is invisible to any prescribed finite set of Mellin values
-- statement:
--   For every prime $p$ and every finite set of complex frequencies $S$, there is a smooth compactly supported complex radial test $\phi$, vanishing outside $(p-1/2,p+1/2)$ and taking value one at $p$. Its Mellin transform vanishes at every point of $S$ and at 0 and 1. All its radial identity samples vanish. Yet its two-sided prime-power sampling functional satisfies $$\sum_{n\ge1}\frac{\Lambda(n)}{\sqrt n}\bigl(\phi(n)+\phi(1/n)\bigr)=\frac{\log p}{\sqrt p}>0.$$ The test has a smooth compactly supported log profile. This separates local sampling from any reconstruction that uses only the indicated finite Mellin data and the radial identity sample.
-- source:
--   Masullo, The Music of the Primes, (10.4.3.50), (11.3.2.1). Strengthens the isolated radial bump test from manuscript issue #1358 and distinguishes it from the scalar Mellin corrections studied in the Prove2Me mission.

import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
open MeasureTheory Set

theorem MasulloRH.isolated_prime_sampling_annihilating_finite_mellin
    (p : ℕ) (hp : p.Prime) (S : Finset ℂ) :
    ∃ f : ℝ → ℂ,
      let φ (x : ℝ) := if 0<x then f (Real.log x) else 0
      ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ f (Real.log p) = 1 ∧
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
      (∀ x : ℝ, x ≤ (p:ℝ)-1/2 ∨ (p:ℝ)+1/2 ≤ x → φ x = 0) ∧
      (∀ n : ℕ, φ n = if n = p then 1 else 0) ∧
      (∀ x : ℝ, 0 < x → φ (x⁻¹*x) = 0) ∧
      HasMellin φ 0 0 ∧ HasMellin φ 1 0 ∧ (∀ z ∈ S, HasMellin φ z 0) ∧
      HasSum (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ):ℂ) *
        (φ n + φ (1/(n:ℝ)))) ((Real.log p / Real.sqrt p : ℝ):ℂ) ∧
      0 < Real.log p / Real.sqrt p := by sorry
