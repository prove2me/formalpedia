-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftIntegrationByParts
-- name    : Kyprianou.Ch01.stableGammaStrictLeftIntegrationByParts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:12:54.513785+00:00
-- url     : https://prove2.me/theorems/95fad3ef-c996-4d5d-9f3c-9ee6eccffba0
-- title:
--   Half-line integration by parts for the complex Gamma stable deficit kernel
-- statement:
--   Exact source half-line integration by parts of (exp(wr)-1)r^(−alpha−1), with 0<alpha<1 and Re(w)<0. The two boundary products vanish, the derivative term is (w/alpha) times the complex Mellin integral.
-- source:
--   Kyprianou (2006) Chapter 1 stable index 0<alpha<1, complex Lévy exponent Gamma transform.

import Mathlib
open MeasureTheory Complex Real Set Filter
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftIntegrationByParts
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hwre : w.re < 0) :
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        ((r ^ (-alpha - 1) : ℝ) : ℂ) ∂volume) =
      (w / (alpha : ℂ)) *
        (∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) := by sorry
