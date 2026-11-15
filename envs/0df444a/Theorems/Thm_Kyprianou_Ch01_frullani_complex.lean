-- Prove2me | Theorems.Thm_Kyprianou_Ch01_frullani_complex
-- name    : Kyprianou.Ch01.frullani_complex
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:09:44.519367+00:00
-- url     : https://prove2.me/theorems/d7bbb940-7548-4446-be57-c040125ada98
-- title:
--   Lemma 1.7: complex Frullani identity for the gamma Lévy exponent
-- statement:
--   Kyprianou (2006), Lemma 1.7, p. 8: for alpha, beta positive and complex z with non-positive real part, the exponential of minus beta times the principal logarithm of (1 - z/alpha) equals the exponential of minus the complex Frullani integral from zero to infinity. Add the actual integrability conclusion to avoid totalised divergent integrals. Equivalent to the book's reciprocal power interpretation on the right half-plane. Existing Prove2Me FamousTheorems.frullani_integral (Proved) is a related real-parameter result, and a complex bridge requires an independent proof.
-- source:
--   A. E. Kyprianou, Introductory Lectures on Fluctuations of Lévy Processes with Applications, 2006, Lemma 1.7, printed p. 8; Exercise 1.3, printed p. 27.

import Mathlib

open MeasureTheory Set
open scoped Real
set_option autoImplicit false

theorem Kyprianou.Ch01.frullani_complex
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    (IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ))) ∧
      Complex.exp (-(β : ℂ) * Complex.log (1 - z / (α : ℂ))) =
        Complex.exp
          (-(∫ x in Ioi (0 : ℝ),
            ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
              ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))) := by
  sorry
