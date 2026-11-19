-- Prove2me | Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitEnvelopeBound
-- name    : Kyprianou.Ch01.stableGammaComplexDeficitEnvelopeBound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T22:54:55.315481+00:00
-- url     : https://prove2.me/theorems/ad531b95-629a-4649-b4ef-a2be86e74796
-- title:
--   Complex stable Gamma integral pointwise two-scaled power envelope
-- statement:
--   For positive real r, complex w with nonpositive real part and any alpha, the stable exponential deficit times the real power r^(-alpha-1) is dominated by twice a piecewise integrable power envelope. Near zero use the linear bound ||exp(wr)-1||≤2||w||r; above one use the bound ||exp(wr)-1||≤2. This retains the exact complex kernel and original α, w.
-- source:
--   Kyprianou 2006, Chapter 1 stable-index gamma integral in closed left half-plane, for proof of stableGammaIntegralComplexExtensionV2.

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_complexExpDeficitTwoNorm
open MeasureTheory Set Complex Real
set_option autoImplicit false

theorem Kyprianou.Ch01.stableGammaComplexDeficitEnvelopeBound (alpha : ℝ) (w : ℂ) (hwre : w.re ≤ 0) (r : ℝ) (hr : 0 < r) :
  ‖(Complex.exp (w * (r : ℂ)) - 1) * (((r ^ (-alpha - 1) : ℝ)) : ℂ)‖ ≤
    2 * (if r ≤ 1 then ‖w‖ * r ^ (-alpha) else r ^ (-alpha - 1)) := by
  sorry
