-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftComplexRealAxisAnchor
-- name    : Kyprianou.Ch01.stableGammaStrictLeftComplexRealAxisAnchor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:36:56.094871+00:00
-- url     : https://prove2.me/theorems/39e1de2b-87fb-4260-9670-4e0cfe75ee16
-- title:
--   Complex Mellin integral identity restricted to negative-real Laplace parameters
-- statement:
--   The source-exact complex Mellin kernel exp(−u r) r^(−alpha) integrated over r>0 equals the real Gamma transform (1/u)^(1−alpha)Gamma(1−alpha), embedded in ℂ, for real u>0 and 0<alpha<1. This is the exact negative-real-axis restriction of the strict-left complex Mellin theorem. It follows by real-to-complex casting and the already Proved real Mellin Gamma anchor. It is the identity-theorem anchor for holomorphic extension.
-- source:
--   Kyprianou (2006) Chapter 1, stable complex Gamma Laplace identity on the real negative axis.

import Mathlib
open MeasureTheory Complex Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftComplexRealAxisAnchor
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      Complex.exp (-(u : ℂ) * (r : ℂ)) *
        ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
      (((((1 / u) ^ (1 - alpha)) * Real.Gamma (1 - alpha) : ℝ)) : ℂ)
    := by sorry
