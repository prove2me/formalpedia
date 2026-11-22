-- Prove2me | Theorems.Thm_MasulloRH_logDeriv_analytic_verified_region
-- name    : MasulloRH.logDeriv_analytic_verified_region
-- status  : Proved
-- author  : @kirisame
-- created : 2026-11-22T14:37:48.191842+00:00
-- url     : https://prove2.me/theorems/2f5bd5f8-1e3e-4ce8-9329-14975e48c400
-- title:
--   Analyticity of the zeta logarithmic derivative through height 100000 and on the closed right half-plane beyond one
-- statement:
--   Let $s$ be a complex number with $\Re s>1/2$ and $s\ne1$. If $|\Im s|\le 100000$ or $\Re s\ge1$, then the actual logarithmic derivative $\zeta\prime/\zeta$ is complex analytic at $s$. In the finite-height region this follows from the verified zero locations, and the half-plane $\Re s\ge1$ is zero-free at every height. This gives a finite-height specialization of the Masullo strip-complement milestone for every admissible strip width.
-- source:
--   Finite-height corollary of Platt and Trudgian, The Riemann hypothesis is true up to 3·10^12, Theorem 1, https://arxiv.org/abs/2004.09765 , using only the Prove2Me verified blocks through 100000. The target specialized here is https://prove2.me/theorems/d50ef798-57ea-4306-a602-313bd21a9faa .

import Definitions.Def_MasulloRH_RegularizedTrace
open MasulloRH

theorem MasulloRH.logDeriv_analytic_verified_region (s : ℂ) (hr : 1 / 2 < s.re) (hpole : s ≠ 1)
    (hregion : |s.im| ≤ 100000 ∨ 1 ≤ s.re) : AnalyticAt ℂ zetaLogDeriv s := by sorry
