-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingRenewalHomogeneousVanish
-- name    : Kyprianou.Ch01.branchingRenewalHomogeneousVanish
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T14:11:59.184798+00:00
-- url     : https://prove2.me/theorems/33b5a5dc-cee3-487b-a483-59cd6f97a0c2
-- title:
--   Bounded solutions of the homogeneous branching renewal equation vanish
-- statement:
--   Let $\lambda>0$ and let $(p_j)_{j\ge 0}$ be an offspring distribution. Suppose $h_y(t,k)$ is a real family, indexed by the initial population, the time, and the observed state, with $|h_y(t,k)|\le 1$ and with $h_0(t,\cdot)=0$. Suppose that for every $y\ge 1$ and every $t>0$ the family satisfies the homogeneous first-jump equation
--   $$
--   h_y(t,k)=\int_0^t \lambda y\, e^{-\lambda y s}\sum_{j=0}^\infty p_j\, h_{y-1+j}(t-s,k)\,ds
--   $$
--   and that the integrand is interval-integrable on $[0,t]$. Then $h_y(t,k)=0$ for every $y$ and every $t>0$.
--
--   The holding term of the renewal equation has cancelled, so this is the linear uniqueness statement for the discounted branching kernel. A bound of $1$ keeps the unknown in the same class as a difference of probability masses.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingRenewalHomogeneousVanish
    (rate : ℝ) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (h : ℕ → ℝ≥0 → ℕ → ℝ)
    (hBound : ∀ y : ℕ, ∀ t : ℝ≥0, ∀ k : ℕ, |h y t k| ≤ 1)
    (hZero : ∀ t : ℝ≥0, ∀ k : ℕ, h 0 t k = 0)
    (hEq : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k)
        volume 0 (t : ℝ) ∧
      h y t k =
        ∫ s in (0 : ℝ)..(t : ℝ),
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              h ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k) :
    ∀ y : ℕ, ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ, h y t k = 0 := by
  sorry
