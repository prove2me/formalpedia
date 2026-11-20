-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftRealMellinAnchor
-- name    : Kyprianou.Ch01.stableGammaStrictLeftRealMellinAnchor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:32:09.583174+00:00
-- url     : https://prove2.me/theorems/e3c7ebc9-5eb1-426d-ac30-3a3ec320fb6d
-- title:
--   Real-axis exact Mellin Gamma integral anchoring the complex Laplace identity
-- statement:
--   For 0<alpha<1 and real u>0, the positive-halfline integral ∫ exp(−ur) r^(−alpha) dr equals (1/u)^(1−alpha) Γ(1−alpha), the exact real-axis restriction of the strict-left complex Mellin identity. It follows from pinned Mathlib Real.integral_rpow_mul_exp_neg_mul_Ioi with a=1−alpha and the exact real exponent identity 1−alpha−1=−alpha. This is the real-axis anchor for a subsequent holomorphic identity-theorem extension.
-- source:
--   Kyprianou (2006), Chapter 1, complex stable Gamma transform, real Laplace axis.

import Mathlib
open MeasureTheory Real Set
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaStrictLeftRealMellinAnchor
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-(u * r)) * r ^ (-alpha) ∂volume) =
      (1 / u) ^ (1 - alpha) * Real.Gamma (1 - alpha) := by sorry
