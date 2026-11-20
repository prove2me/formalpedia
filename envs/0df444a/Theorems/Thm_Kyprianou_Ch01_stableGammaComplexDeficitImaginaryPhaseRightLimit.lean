-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitImaginaryPhaseRightLimit
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitImaginaryPhaseRightLimit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:51:46.449452+00:00
-- url     : https://prove2.me/theorems/859176e4-cd83-4e93-a42f-250725831c21
-- title:
--   Stable complex Gamma principal-log phase is continuous approaching the imaginary axis (damping limit)
-- statement:
--   For 0<alpha<1 and nonzero imaginary w, the principal complex-log phase exp(alpha*log(-w+epsilon)) converges to exp(alpha*log(-w)) as positive epsilon↓0. Since -w lies away from the principal logarithm branch cut, this is a true continuity result with no change of branch.
-- source:
--   Kyprianou (2006), Chapter 1 stable α∈(0,1) complex Gamma integral at nonzero imaginary parameters, strict-left limit.

import Mathlib
open MeasureTheory Set Complex Real Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitImaginaryPhaseRightLimit
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re = 0) (hwim : w.im ≠ 0) :
    Tendsto
      (fun epsilon : ℝ =>
        Complex.exp ((alpha : ℂ) *
          Complex.log (-(w - (epsilon : ℂ)))))
      ((nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ))))
      (nhds (Complex.exp ((alpha : ℂ) * Complex.log (-w)))) := by
  sorry
