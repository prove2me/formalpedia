-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftMellinIntegrable
-- name    : Kyprianou.Ch01.stableGammaStrictLeftMellinIntegrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:14:34.347644+00:00
-- url     : https://prove2.me/theorems/a44bb598-b4bd-403e-934d-25e4562b3f02
-- title:
--   Absolute integrability of the strict-left complex exponential Mellin kernel
-- statement:
--   For 0<alpha<1 and Re(w)<0, the source complex Mellin kernel exp(wr)r^(−alpha) is absolutely Lebesgue integrable over r>0. Its norm is exactly r^(−alpha)*exp(−(−Re(w))*r), dominated by the pinned Mathlib GaussianIntegral.integrableOn_rpow_mul_exp_neg_mul_rpow (with p=1, s=−alpha, b=−Re(w)). This integrability is the nontrivial second integrability condition in the strict-left Gamma deficit integration-by-parts formula.
-- source:
--   Kyprianou (2006) Chapter 1 stable α<1 complex Gamma integral, Mellin source.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftMellinIntegrable
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    IntegrableOn
      (fun r : ℝ => Complex.exp (w * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) := by sorry
