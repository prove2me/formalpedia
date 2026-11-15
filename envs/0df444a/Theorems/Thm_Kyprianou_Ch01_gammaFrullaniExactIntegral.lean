-- Prove2me | Theorems.Thm_Kyprianou_Ch01_gammaFrullaniExactIntegral
-- name    : Kyprianou.Ch01.gammaFrullaniExactIntegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:07:26.133677+00:00
-- url     : https://prove2.me/theorems/8ef4fa65-5a8b-4799-be6f-fad076b13cbd
-- title:
--   Kyprianou §1.2.4: complex logarithmic Frullani integral for the gamma Lévy exponent
-- statement:
--   The integral of (1 - exp(zx)) beta exp(-alpha x)/x on the positive half-line equals beta log(1-z/alpha) for alpha,beta>0 and Re(z)<=0, using the principal complex logarithm. This is the full identity before exponentiation needed for the gamma Lévy characteristic exponent.
-- source:
--   Kyprianou (2006), Chapter 1, §1.2.4, gamma subordinator and Frullani identity; derived from Cohn–Elkies complex Frullani kernel theorem.

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_integral_complexFrullaniKernel

open MeasureTheory Filter Set CohnElkies
open scoped Topology
set_option autoImplicit false

/-- Stronger logarithmic integral identity, before exponentiation. -/
theorem Kyprianou.Ch01.gammaFrullaniExactIntegral
    (α β : ℝ) (z : ℂ) (hα : 0 < α) (hβ : 0 < β) (hz : z.re ≤ 0) :
    (∫ x in Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (z * (x : ℂ))) *
        ((β : ℂ) * Complex.exp (-(α : ℂ) * (x : ℂ)) / (x : ℂ))) =
      (β : ℂ) * Complex.log (1 - z / (α : ℂ)) := by sorry
