-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricMeasureInfinitelyDivisible
-- name    : Kyprianou.Ch01.geometricMeasureInfinitelyDivisible
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:34:23.956493+00:00
-- url     : https://prove2.me/theorems/e2759142-d23d-46c1-834c-e7638cea9ea9
-- title:
--   Canonical geometric counting measure is infinitely divisible for all positive success parameters
-- statement:
--   For every geometric success parameter p in the unit interval with p>0, the corresponding canonical geometric counting law on nonnegative integers, mapped into the reals, is infinitely divisible in the exact LevyFoundations convolution-root sense. A source-faithful proof constructs the discrete compound Poisson representation of a geometric random variable: for p<1 the intensity is -log(p), and jumps have the logarithmic-series distribution proportional to (1-p)^k/k for strictly positive integers k. The resulting compound Poisson Fourier exponent equals log[p/(1-(1-p)e^(iξ))], matching the canonical geometric characteristic function. The case p=1 is the Dirac mass at zero and is infinitely divisible. This is the only remaining stochastic infinite-divisibility obligation after the separately proved exact geometric measure identification and complex generating function.
-- source:
--   Kyprianou (2006), Chapter 1 Exercise 1.2(i) and solution printed p. 299; Mathlib geometricMeasure, geometric characteristic function, compound-Poisson distributions; LevyFoundations.isInfinitelyDivisibleLaw.

import Mathlib
import Definitions.Def_levy_foundations_isInfinitelyDivisibleLaw
open MeasureTheory ProbabilityTheory LevyFoundations
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricMeasureInfinitelyDivisible
    (p : unitInterval.Elem) (hp : p ≠ 0) :
    LevyFoundations.isInfinitelyDivisibleLaw
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) := by sorry
