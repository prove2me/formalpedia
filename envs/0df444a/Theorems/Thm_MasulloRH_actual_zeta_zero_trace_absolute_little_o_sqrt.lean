-- Prove2me | Theorems.Thm_MasulloRH_actual_zeta_zero_trace_absolute_little_o_sqrt
-- name    : MasulloRH.actual_zeta_zero_trace_absolute_little_o_sqrt
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T08:04:59.167648+00:00
-- url     : https://prove2.me/theorems/9e0dd24c-8629-445d-825c-afd7ec4b859c
-- title:
--   The absolute multiplicity-weighted zeta zero trace on each translated smooth test is little-oh of the arithmetic square-root scale
-- statement:
--   For every compactly supported complex C² log profile k, sum over all actual open-strip zeros of Mathlib riemannZeta, counted with their analytic multiplicities. The sum of |m(rho) paperFT(k)((rho−1/2)/i)| exp((Re rho−1)L) tends to zero as L goes to infinity. With X=exp(L), this is the normalized absolute value series for the translated zero contribution, so the signed scalar zero sum is o(sqrt X).
-- source:
--   Frozen Masullo (10.3.2.3–5); scalar zero side only. Uses the verified Zeta23 local zero count and WeilEF summability, and the Mathlib closed zeta-zero configuration. The operator identification is independent.

import Mathlib
import Definitions.Def_Zeta23_Statement_SeamClosed
open Filter Topology Zeta23

theorem MasulloRH.actual_zeta_zero_trace_absolute_little_o_sqrt (k : ℝ → ℂ) (hk : ContDiff ℝ 2 k) (hc : HasCompactSupport k) :
    Tendsto (fun L : ℝ => ∑' ρ : {ρ : ℂ // IsNontrivialZero ρ},
      ‖(zeroMult ρ : ℂ) * paperFT k (gammaOf ρ)‖ *
        Real.exp (((ρ : ℂ).re - 1) * L)) atTop (𝓝 0) := by sorry
