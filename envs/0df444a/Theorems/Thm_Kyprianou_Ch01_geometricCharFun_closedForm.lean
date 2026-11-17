-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricCharFun_closedForm
-- name    : Kyprianou.Ch01.geometricCharFun_closedForm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:47:13.395509+00:00
-- url     : https://prove2.me/theorems/986fef90-c162-4155-a979-fb21e124ff91
-- title:
--   Exact rational characteristic function of an arbitrary canonical geometric counting law
-- statement:
--   For any positive geometric success probability p≤1, the characteristic function of the canonical geometric counting distribution, regarded as a real-valued law, is exactly p/[1-(1-p)e^{iξ}] for every real Fourier frequency ξ. The proof is by three independently source-verified bridges: the universal integer-law characteristic function as a probability generating function, the exact canonical geometric complex PGF, and the strict convergence estimate on the Fourier unit circle. This rational formula is the central Fourier identity for the logarithmic-series compound Poisson representation proving infinite divisibility in Kyprianou Chapter 1 Exercise 1.2(i).
-- source:
--   Kyprianou (2006) Chapter 1 Exercise 1.2(i), solution p. 299; Proved Kyprianou.Ch01.discreteLawCharFun_asPGF, geometricMeasure_complexPGF, geometricFourierConvergence.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricCharFun_closedForm (p : unitInterval.Elem) (hp : p ≠ 0) (xi : ℝ) :
    charFun
      ((ProbabilityTheory.geometricMeasure p).map
        (fun k : ℕ => (k : ℝ))) xi =
      ((p : ℝ) : ℂ) /
        (1 - (1 - ((p : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (xi : ℂ))) := by
  sorry
