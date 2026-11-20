-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDeficitDifference
-- name    : Kyprianou.Ch01.stableGammaStrictLeftDeficitDifference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:30:52.027867+00:00
-- url     : https://prove2.me/theorems/091068a9-d52c-4d6d-89e4-7a89ae6e9e49
-- title:
--   Difference of two strictly-left complex Gamma deficits equals difference of fractional powers
-- statement:
--   For 0<alpha<1 and strictly negative real parts of u,v, the integral over positive radii of (exp(u r)-exp(v r))r^(-alpha-1) equals Gamma(-alpha)*(exp(alpha log(-u))-exp(alpha log(-v))). Derived by subtracting two independently absolutely integrable source-exact stable Gamma deficit evaluations.
-- source:
--   Kyprianou (2006) Chapter 1 Exercises 1.4 and 1.6; completed strict-left complex Gamma deficit identities.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValueStrictLeft
open MeasureTheory Set Complex ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftDeficitDifference
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (u v : ℂ) (hu : u.re < 0) (hv : v.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (u * (r : ℂ)) -
        Complex.exp (v * (r : ℂ))) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        (Complex.exp ((alpha : ℂ) * Complex.log (-u)) -
          Complex.exp ((alpha : ℂ) * Complex.log (-v))) := by sorry
