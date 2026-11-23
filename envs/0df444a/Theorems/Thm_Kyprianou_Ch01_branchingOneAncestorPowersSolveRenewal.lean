-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingOneAncestorPowersSolveRenewal
-- name    : Kyprianou.Ch01.branchingOneAncestorPowersSolveRenewal
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:58:06.055793+00:00
-- url     : https://prove2.me/theorems/82acd82f-5955-4985-abb2-1e547d400af4
-- title:
--   Convolution powers of the one-ancestor law solve the renewal equation
-- statement:
--   Let $\lambda>0$ and let $(p_j)_{j\ge 0}$ be an offspring distribution. Suppose $K_y(t)$ is a family of probability mass functions with $K_0(t)=\delta_0$, satisfying the first-jump renewal equation of a continuous-time branching process for every $y\ge 1$ and every $t>0$. Define $C_0(t)=\delta_0$ and $C_{y+1}(t)=C_y(t)*K_1(t)$, the $y$-fold convolution of the one-ancestor law at the same time. Then $C$ satisfies the same renewal equation: for $y\ge 1$ and $t>0$,
--   $$
--   C_y(t)=e^{-\lambda y t}\delta_y+\int_0^t \lambda y\, e^{-\lambda y s}\sum_{j=0}^\infty p_j\, C_{y-1+j}(t-s)\,ds,
--   $$
--   and the integrand is interval-integrable on $[0,t]$.
--
--   Combined with uniqueness of honest solutions, this identifies $K_y(t)$ with the $y$-fold convolution of $K_1(t)$.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingOneAncestorPowersSolveRenewal
    (rate : ℝ) (hrate : 0 < rate)
    (offspring : PMF ℕ)
    (K : PopulationLaws)
    (hZero : ∀ t : ℝ≥0, ∀ k : ℕ, K 0 t k = (PMF.pure 0) k)
    (hRenew : ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
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
    (C : PopulationLaws)
    (hC0 : ∀ t : ℝ≥0, C 0 t = PMF.pure 0)
    (hCSucc : ∀ y : ℕ, ∀ t : ℝ≥0,
      C (y + 1) t =
        (C y t).bind (fun n => (K 1 t).map (fun m => n + m))) :
    ∀ y : ℕ, 0 < y → ∀ t : ℝ≥0, 0 < t → ∀ k : ℕ,
      IntervalIntegrable
        (fun s : ℝ =>
          (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
            ∑' j : ℕ, (offspring j).toReal *
              (C ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal)
        volume 0 (t : ℝ) ∧
      (C y t k).toReal =
        (if k = y then Real.exp (-(rate * (y : ℝ) * (t : ℝ))) else 0) +
          ∫ s in (0 : ℝ)..(t : ℝ),
            (rate * (y : ℝ)) * Real.exp (-((rate * (y : ℝ)) * s)) *
              ∑' j : ℕ, (offspring j).toReal *
                (C ((y - 1) + j) (Real.toNNReal ((t : ℝ) - s)) k).toReal := by
  sorry
