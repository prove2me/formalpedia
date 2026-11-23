-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingRenewalSolutionUnique
-- name    : Kyprianou.Ch01.branchingRenewalSolutionUnique
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:58:05.398026+00:00
-- url     : https://prove2.me/theorems/c395821c-d2a0-4494-80ae-288521d7ccf5
-- title:
--   Honest solutions of the branching renewal equation agree
-- statement:
--   Let $\lambda>0$ and let $(p_j)_{j\ge 0}$ be a probability distribution on the nonnegative integers. Suppose $K$ and $L$ are two families of probability mass functions on $\mathbb{N}$, indexed by the initial population and by time, and that both are concentrated at $0$ when the initial population is $0$. Suppose that for every initial population $y\ge 1$ and every time $t>0$ both families satisfy the first-jump renewal equation
--   $$
--   \mu_y(t)=e^{-\lambda y t}\delta_y+\int_0^t \lambda y\, e^{-\lambda y s}\sum_{j=0}^\infty p_j\, \mu_{y-1+j}(t-s)\,ds
--   $$
--   and that the integrand is interval-integrable on $[0,t]$. Then $K_y(t)=L_y(t)$ for every $y$ and every $t>0$.
--
--   The equation is a linear Volterra system on the population index. Within the class of probability mass functions the Neumann iteration has only one limit, so an honest solution is unique.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingRenewalSolutionUnique
    (rate : ℝ) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (K L : PopulationLaws)
    (hKZero : ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k)
    (hLZero : ∀ t : ℝ≥0, ∀ k : ℕ, L 0 t k = (PMF.pure 0) k)
    (hKRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (K y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (K ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
    (hLRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (L y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (L ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal) :
    ∀ y : ℕ, ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ, K y t k = L y t k := by
  sorry
