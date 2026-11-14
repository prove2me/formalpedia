-- Prove2me | Theorems.Thm_KSATSingleFlip_Connect_poisson_two_sided_tail
-- name    : KSATSingleFlip.Connect.poisson_two_sided_tail
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:45:21.918592+00:00
-- url     : https://prove2.me/theorems/3d8f79f4-335f-4e76-9d1d-548d9b149f73
-- title:
--   Two-sided Poisson tail for the clause-count concentration proof
-- statement:
--   For N with Poisson mean r > 0 and x > 0, the probability that |N−r| is at least x is at most 2 exp(−x²/(8(r+x))). This deliberately relaxed bound covers deviations smaller or larger than the mean and is sufficient for the Poisson-count part of Lemma 2.6.
-- source:
--   Wang–Yin–Yu–Zhang, Single-Variable Connectivity in Random k-SAT, Lemma 2.6, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/737.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem KSATSingleFlip.Connect.poisson_two_sided_tail (r : ℝ≥0) (hr : 0 < r) (x : ℝ) (hx : 0 < x) :
    (poissonMeasure r).real {k : ℕ | x ≤ |(k:ℝ)-(r:ℝ)|} ≤
      2*Real.exp (-(x^2)/(8*((r:ℝ)+x))) := by sorry
