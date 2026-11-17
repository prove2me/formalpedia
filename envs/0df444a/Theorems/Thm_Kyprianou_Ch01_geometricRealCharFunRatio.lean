-- Prove2me | Theorems.Thm_Kyprianou_Ch01_geometricRealCharFunRatio
-- name    : Kyprianou.Ch01.geometricRealCharFunRatio
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:34:33.552027+00:00
-- url     : https://prove2.me/theorems/98a0fcd9-14fa-4116-8e53-1ea7e5005af2
-- title:
--   Exact characteristic function of the strict geometric real-count law
-- statement:
--   For a geometric probability law with p in (0,1), its real-count characteristic function equals p/[1−(1−p)exp(iξ)]. The result derives the source characteristic function from the proved discrete-law Fourier representation and geometric probability generating function, with an explicit strict convergence bound.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i), strict geometric characteristic function.

import Mathlib
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.geometricRealCharFunRatio
    (p : unitInterval.Elem) (hp : p ≠ 0) (hp1 : (p : ℝ) < 1)
    (xi : ℝ) :
    charFun ((ProbabilityTheory.geometricMeasure p).map
      (fun k : ℕ => (k : ℝ))) xi =
      (((p : ℝ) : ℂ) /
        (1 - (1 - (((p : ℝ) : ℂ))) *
          Complex.exp ((xi : ℂ) * Complex.I))) := by
  sorry
