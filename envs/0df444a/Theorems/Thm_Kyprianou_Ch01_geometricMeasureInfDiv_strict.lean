-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMeasureInfDiv_strict
-- name    : Kyprianou.Ch01.geometricMeasureInfDiv_strict
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:45:30.846572+00:00
-- url     : https://prove2.me/theorems/49fa322e-a90b-42c8-a56d-131ae9346c3c
-- title:
--   Strict geometric infinite divisibility from the logarithmic-series compound Poisson representation
-- statement:
--   For the genuinely nondegenerate geometric parameter 0<p<1, construct for every positive convolution order n a probability measure whose n-fold real convolution is the canonical geometric counting law. The probability generating function of the target is p/(1-(1-p)z), with logarithm the compensated logarithmic-series generating function λ∑_{k≥1}[(1-p)^k/(kλ)](z^k-1), λ=-log p>0. The source-faithful proof constructs the compound Poisson law on strictly positive integer jumps with logarithmic jump mass proportional to (1-p)^k/k; splitting the Poisson intensity by n yields n independent convolution roots. The previously Proved complex PGF and discrete Fourier-embedding identity validate equality of laws via characteristic functions. The distinct boundary case p=1 is solved independently by Dirac-zero convolution roots, so this theorem is precisely the remaining mathematical core of Chapter 1 Exercise 1.2(i).
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i) solution printed p. 299; pinned Mathlib geometricMeasure, probability generating function and compound Poisson; LevyFoundations.isInfinitelyDivisibleLaw.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMeasureInfDiv_strict
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) := by sorry
