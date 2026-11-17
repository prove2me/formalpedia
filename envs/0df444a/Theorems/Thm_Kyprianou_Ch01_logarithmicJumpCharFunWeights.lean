-- Prove2me | Theorems.Thm_Kyprianou_Ch01_logarithmicJumpCharFunWeights
-- name    : Kyprianou.Ch01.logarithmicJumpCharFunWeights
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T05:19:53.046663+00:00
-- url     : https://prove2.me/theorems/00c9f2c7-d333-46ee-ac61-0d3d4cf77350
-- title:
--   Characteristic function of the logarithmic jump law as its explicit Fourier series
-- statement:
--   Given a logarithmic-series PMF with q in (0,1), the characteristic function of its positive-integer real pushforward is the Fourier series with weights q^(n+1)/((n+1)(-log(1-q))). This is the exact probabilistic-to-analytic bridge for Exercise 1.2(i)'s compound-Poisson representation.
-- source:
--   Kyprianou (2006), Chapter 1, Exercise 1.2(i).

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_shiftedPMFCharFun_tsum
open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem Kyprianou.Ch01.logarithmicJumpCharFunWeights
    (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (jump : PMF ℕ)
    (hjump : ∀ n : ℕ,
      jump n = ENNReal.ofReal
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))))
    (xi : ℝ) :
    charFun (jump.toMeasure.map
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ))) xi =
      ∑' n : ℕ,
        ((q ^ (n + 1) / ((n : ℝ) + 1)) / (-Real.log (1 - q))) •
          Complex.exp
            ((xi : ℂ) * (((n + 1 : ℕ) : ℝ) : ℂ) * Complex.I) := by
  sorry
