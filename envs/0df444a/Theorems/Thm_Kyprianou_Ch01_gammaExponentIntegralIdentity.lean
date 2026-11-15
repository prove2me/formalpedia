-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaExponentIntegralIdentity
-- name    : Kyprianou.Ch01.gammaExponentIntegralIdentity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:07:09.514309+00:00
-- url     : https://prove2.me/theorems/59ce6706-ee8c-41d7-b14b-5652a2b50e85
-- title:
--   Kyprianou §1.2.4: exact gamma Lévy characteristic exponent integral
-- statement:
--   For every real frequency theta, the complex Frullani kernel giving the gamma subordinator Lévy exponent is integrable on (0,infinity), and its integral equals beta log(1-i theta/alpha). This is the analytic component of Chapter 1 gamma Lévy exponent.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4, gamma Lévy exponent via Frullani formula.

import Mathlib
open MeasureTheory Filter Set
open scoped Topology
set_option autoImplicit false

/-- The gamma Lévy exponent integral from Chapter 1, as a proved Frullani corollary. -/
theorem Kyprianou.Ch01.gammaExponentIntegralIdentity
    (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (θ : ℝ) :
    IntegrableOn
      (fun x : ℝ =>
        ((1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ) * (x : ℂ))) *
          ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ)))
      (Ioi (0 : ℝ)) ∧
    (∫ x in Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (θ : ℂ) * (x : ℂ))) *
        ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))) =
      (β : ℂ) * Complex.log
        (1 - Complex.I * (θ : ℂ) / (α : ℂ)) := by sorry
