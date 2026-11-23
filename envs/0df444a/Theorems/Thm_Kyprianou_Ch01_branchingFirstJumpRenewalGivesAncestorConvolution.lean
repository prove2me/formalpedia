-- Prove2me | Theorems.Thm_Kyprianou_Ch01_branchingFirstJumpRenewalGivesAncestorConvolution
-- name    : Kyprianou.Ch01.branchingFirstJumpRenewalGivesAncestorConvolution
-- status  : Open
-- author  : @pageman
-- created : 2026-11-23T13:20:32.874486+00:00
-- url     : https://prove2.me/theorems/f2d2afe0-1dab-4008-bfae-2fdce996d876
-- title:
--   A probability solution of the branching renewal equation has independent ancestors
-- statement:
--   Let $K_y(t)$ be any family of probability mass functions on the nonnegative integers, indexed by the initial population $y$ and the time $t$. Assume $K_0(t)=\delta_0$, and assume that every positive initial population satisfies the first-jump renewal equation of a continuous-time binary-clock branching process with life rate $\lambda>0$ and offspring law $p$: the holding probability at $y$ is $e^{-\lambda y t}$, and a jump at time $s$ to $y-1+j$ is followed by an independent copy of $K_{y-1+j}$ over the remaining time. Then for every $t>0$ and all initial counts $a,b$,
--   $$K_{a+b}(t)=K_a(t)*K_b(t),$$
--   the convolution of probability mass functions. The argument is analytic: an honest probability solution of this renewal equation is unique, and the convolution powers of the one-ancestor law solve the same equation. No path space and no offspring moment are used.
-- source:
--   A. E. Kyprianou, Fluctuations of Levy Processes with Applications, 2nd ed., Springer, Chapter 1, reverse Lamperti representation and the branching property.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal BigOperators Interval
set_option autoImplicit false

theorem Kyprianou.Ch01.branchingFirstJumpRenewalGivesAncestorConvolution
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
    (a b : ℕ) (t : ℝ≥0) (ht : 0 < t) (k : ℕ) :
    K (a + b) t k =
      ((K a t).bind (fun n => (K b t).map (fun m => n + m))) k := by
  sorry
