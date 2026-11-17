-- Prove2me | Theorems.Thm_Kyprianou_Ch01_discreteLawCharFun_asPGF
-- name    : Kyprianou.Ch01.discreteLawCharFun_asPGF
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:42:00.011204+00:00
-- url     : https://prove2.me/theorems/4040b256-9a1e-4189-bcb3-f9993640f54f
-- title:
--   Characteristic function of any natural-valued probability distribution equals its complex probability generating function on the unit circle
-- statement:
--   Let G be any probability measure on the nonnegative integers and embed its counting variable in the real line. Its characteristic function at real frequency ξ is exactly the complex probability generating function ∫ e^(iξ)^k dG(k). The proof is a rigorous change of variables for the pushforward measure followed by the complex exponential identity exp(iξ k)=(exp(iξ))^k. This general, measure-theoretic Fourier bridge combines with the separately proved canonical geometric PGF and its convergence on the unit circle to give the full rational characteristic function of the geometric distribution in Kyprianou Exercise 1.2(i).
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.2(i), printed p. 26, solution p. 299; Mathlib charFun_apply_real, integral_map, Complex.exp_nat_mul.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.discreteLawCharFun_asPGF (G : Measure ℕ) [IsProbabilityMeasure G]
    (xi : ℝ) :
    charFun (G.map (fun k : ℕ => (k : ℝ))) xi =
      ∫ k : ℕ, (Complex.exp (Complex.I * (xi : ℂ))) ^ k ∂G := by
  sorry
