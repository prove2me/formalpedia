-- Prove2me | Theorems.Thm_Kyprianou_Ch01_pmfLaplaceConvolution
-- name    : Kyprianou.Ch01.pmfLaplaceConvolution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:20:40.698053+00:00
-- url     : https://prove2.me/theorems/5e6d9b7e-8242-46f4-a2b1-b98c9a18420d
-- title:
--   PMF convolution Laplace-transform multiplicativity
-- statement:
--   For any two probability mass functions on natural numbers and positive Laplace parameter, the Laplace transform of the law of the sum of two independent draws equals the product of their respective Laplace transforms. The sum law is expressed by the canonical PMF monadic bind and addition map.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.11(i); a general distributional convolution identity underlying branching-process Laplace-factorisation, compatible with Mathlib PMF.bind_apply and IndepFun.mgf_add.

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem Kyprianou.Ch01.pmfLaplaceConvolution
    (p q : PMF ℕ) (phi : ℝ) (hphi : 0 < phi) :
    (∑' n : ℕ, ((p.bind (fun k => q.map (fun m => k + m))) n).toReal *
       Real.exp (-phi * (n : ℝ))) =
      (∑' k : ℕ, (p k).toReal * Real.exp (-phi * (k : ℝ))) *
      (∑' m : ℕ, (q m).toReal * Real.exp (-phi * (m : ℝ))) := by sorry
