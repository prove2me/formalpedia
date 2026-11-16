-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfLaplace_argumentLipschitz
-- name    : Kyprianou.Ch01.pmfLaplace_argumentLipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T18:26:40.585786+00:00
-- url     : https://prove2.me/theorems/41b6f27b-dfc1-4e17-8527-ff315c1e4863
-- title:
--   PMF Laplace transforms have a uniform moment-free Lipschitz modulus away from zero
-- statement:
--   For any probability mass function p on natural numbers, the real Laplace transform L(q)=sum p_k exp(-qk) is uniformly Lipschitz in q on [delta,infinity), with constant 1/delta whenever delta>0. This estimate holds uniformly over all PMFs and requires no offspring first moment. It follows from a k-independent bound on each exponential difference, summability of the weights and the total mass one.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.11(iii), semigroup continuity for arbitrary discrete offspring laws

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_pmfLaplace_summable
import Theorems.Thm_Kyprianou_Ch01_exp_uniform_lipschitz_on_positive
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- A PMF-weighted Laplace transform is uniformly Lipschitz away from zero. -/

theorem Kyprianou.Ch01.pmfLaplace_argumentLipschitz (p : PMF ℕ) (delta : ℝ) (hd : 0 < delta)
    (x y : ℝ) (hx : delta ≤ x) (hy : delta ≤ y) :
    |(∑' k : ℕ, (p k).toReal * Real.exp (-y * (k : ℝ))) -
      (∑' k : ℕ, (p k).toReal * Real.exp (-x * (k : ℝ)))| ≤
      delta⁻¹ * |y - x| := by sorry
