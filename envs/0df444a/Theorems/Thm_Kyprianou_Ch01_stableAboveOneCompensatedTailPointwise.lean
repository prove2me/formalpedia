-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableAboveOneCompensatedTailPointwise
-- name    : Kyprianou.Ch01.stableAboveOneCompensatedTailPointwise
-- status  : Open
-- author  : @WillR
-- created : 2026-11-19T22:25:37.338763+00:00
-- url     : https://prove2.me/theorems/5b12d4ef-be69-4287-b2b9-cbe677cb9497
-- title:
--   Exact positive stable compensated cutoff decomposition into untruncated Fourier and tail moment
-- statement:
--   For r>0, the source positive-jump compensated stable integrand splits into the untruncated Fourier remainder and the original large-jump correction, supported on r>=1. This follows exactly from the independent pointwise source compensation identity and r^(-alpha-1)*r=r^-alpha. Holds for every real alpha, c, xi.
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.4 original truncated Lévy-Khintchine jump integrand.

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Real Complex Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableAboveOneCompensatedTailPointwise
    (alpha c xi r : ℝ) (hr : 0 < r) :
    (c * r ^ (-alpha - 1)) •
      ProbabilityTheory.levyCompensatedIntegrand xi r =
      (c : ℂ) *
        ((Complex.exp ((Complex.I * (xi : ℂ)) * (r : ℂ)) - 1 -
            Complex.I * (xi : ℂ) * (r : ℂ)) *
          (((r ^ (-alpha - 1) : ℝ) : ℂ))) +
      (Complex.I * ((c * xi : ℝ) : ℂ)) *
        (if r < 1 then (0 : ℂ) else
          (((r ^ (-alpha) : ℝ) : ℂ))) := by sorry
