-- Prove2me | Theorems.Thm_MasulloRH_translated_half_weight_prime_power_sum_and_nonvanishing
-- name    : MasulloRH.translated_half_weight_prime_power_sum_and_nonvanishing
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:55:23.690078+00:00
-- url     : https://prove2.me/theorems/f2d1cdcf-dc61-4c31-ba7e-e336d378ddb3
-- title:
--   The arithmetic half-weight shell has leading coefficient M(1/2), for a test with two vanishing moments
-- statement:
--   Fix $0<a\le b$ and a real $C^1$ norm test $f$ with support compactly contained in $(a,b)$. With $\Lambda$ the actual von Mangoldt function and $\mathcal M$ the Mellin transform, the normalized sum $X^{-1/2}\sum_{aX<n\le bX}\Lambda(n)n^{-1/2} f(n/X)$ converges to $\mathcal M f(1/2)=\int_a^b f(t)t^{-1/2}\,dt$ as real $X\to\infty$. This is the full prime-power side on these dilates. Moreover there is a single smooth real $f$ supported in $(1,32)$ with $\mathcal M f(1)=\mathcal M f(-1/2)=0$ for which the unnormalized prime-power sum is at least $c\sqrt X$, with $c>0$, for every sufficiently large $X$. The target is an arithmetic asymptotic relevant to the critical-width trace comparison.
-- source:
--   Masullo, The Music of the Primes, (11.3.2.1), (11.3.2.5) and the half-weighted prime-power side of (12.5.1.1), positive-norm tests for the rational trivial character. Applications of the ordinary prime number theorem. Uses Yuxuan Xu’s verified Chebyshev PNT (2ccce2b3-fbf8-419b-9ad4-52a6c527fd25), the proved MediumPNT it imports, and Yi’s verified smooth Mellin discriminator (47f46585-d134-434c-909e-0b58cfc6b201).

import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Filter MeasureTheory Set
open scoped Topology ArithmeticFunction

theorem MasulloRH.translated_half_weight_prime_power_sum_and_nonvanishing :
    (∀ (a b : ℝ), 0 < a → a ≤ b → ∀ f : ℝ → ℝ, ContDiff ℝ 1 f →
      tsupport f ⊆ Set.Ioo a b →
      Tendsto (fun X : ℝ =>
        (∑ n ∈ Finset.Ioc ⌊a*X⌋₊ ⌊b*X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) / Real.sqrt X)
        atTop (𝓝 ((mellin (fun t => (f t : ℂ)) (1/2 : ℂ)).re))) ∧
    (∃ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ tsupport f ⊆ Set.Ioo 1 32 ∧
      HasMellin (fun t => (f t : ℂ)) 1 0 ∧ HasMellin (fun t => (f t : ℂ)) (-(1/2) : ℂ) 0 ∧
      ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
        c * Real.sqrt X ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊32*X⌋₊,
          ArithmeticFunction.vonMangoldt n / Real.sqrt n * f ((n:ℝ)/X)) := by sorry
