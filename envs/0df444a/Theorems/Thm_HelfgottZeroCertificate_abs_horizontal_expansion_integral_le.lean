-- Prove2me | Theorems.Thm_HelfgottZeroCertificate_abs_horizontal_expansion_integral_le
-- name    : HelfgottZeroCertificate.abs_horizontal_expansion_integral_le
-- status  : Proved
-- author  : @flyingviper
-- created : 2026-11-18T11:59:48.889863+00:00
-- url     : https://prove2.me/theorems/cc699654-f36c-468e-b83e-9ae0ddfdef4f
-- title:
--   Horizontal integral bound from a finite pole expansion and a bounded remainder
-- statement:
--   Let $S$ be a finite set of complex numbers with nonnegative weights $m_\rho$, and let $a,b,v,C$ be real numbers. Suppose $F$ is integrable on the interval from $a$ to $b$ and, throughout the unoriented closed interval between its endpoints,
--
--   $$\left|F(x)-\sum_{\rho\in S}m_\rho\operatorname{Im}(x+iv-\rho)^{-1}\right|\le C.$$
--
--   Then
--
--   $$\left|\int_a^b F(x)\,dx\right|\le\pi\sum_{\rho\in S}m_\rho+C|b-a|.$$
--
--   This converts a local partial-fraction estimate into a horizontal argument-integral bound. The statement permits either endpoint order and poles on the horizontal line; complex inversion is totalized, and such poles contribute zero to the imaginary integrand.
-- source:
--   Original formalization developed for explicit zero-count estimates in the Prove2Me Weak Goldbach project. Source upstream/Solutions/HorizontalPoleIntegral.lean; SHA256 da6ecc35c5e5d8a0877ad2a0cda5660ad5549e0080e566f0f7bf5dd2da88a2ce. Supporting proof is included in the immutable solution submission. Standard arctangent integration / intermediate-value arguments; no claim of a new mathematical theorem.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic
open Complex MeasureTheory Set
open scoped BigOperators

theorem HelfgottZeroCertificate.abs_horizontal_expansion_integral_le :
∀ (S : Finset ℂ) (m : ℂ → ℝ),
  (∀ ρ ∈ S, 0 ≤ m ρ) →
    ∀ (a b v C : ℝ) (F : ℝ → ℝ),
      IntervalIntegrable F MeasureTheory.volume a b →
        (∀ x ∈ Set.uIcc a b, |F x - ∑ ρ ∈ S, m ρ * ({ re := x, im := v } - ρ)⁻¹.im| ≤ C) →
          |∫ (x : ℝ) in a..b, F x| ≤ Real.pi * ∑ ρ ∈ S, m ρ + C * |b - a| := by sorry
