-- Prove2me | Theorems.Thm_MomentSearch_gamma_half_shift_stirling_bounds
-- name    : MomentSearch.gamma_half_shift_stirling_bounds
-- status  : Proved
-- author  : @nmegow
-- created : 2026-11-20T23:25:04.250183+00:00
-- url     : https://prove2.me/theorems/c6247d2c-fbde-4a2a-8c63-27abb37e49d3
-- title:
--   Stirling bounds for the half-shifted Gamma function
-- statement:
--   For $t\ge0$ the half-shifted Gamma function satisfies
--   $$
--   \sqrt\pi\,e^{t\log t-t}\le\Gamma(t+1/2)\le\sqrt{2\pi}\,e^{t\log t-t}.
--   $$
--   The endpoint uses $t\log t=0$ at zero. One proof bounds the normalized ratio by its two endpoint limits. Its logarithmic derivative on $(0,\infty)$ is $\psi(t+1/2)-\log t$, which is positive by the Laplace representation with kernel $1/s-1/(2\sinh(s/2))$. The ratio at zero is $\Gamma(1/2)=\sqrt\pi$, and its limit at infinity is $\sqrt{2\pi}$ by the shifted Stirling asymptotic.
-- source:
--   Digamma Laplace representation: https://doi.org/10.1186/s13660-015-0674-8, equations (1.10) and (2.2). Shifted Stirling asymptotic: NIST DLMF, https://dlmf.nist.gov/5.11.E8, h=1/2.

import Mathlib

theorem MomentSearch.gamma_half_shift_stirling_bounds (t : ℝ) (ht : 0 ≤ t) :
    Real.sqrt Real.pi * Real.exp (t * Real.log t - t) ≤ Real.Gamma (t + 1 / 2) ∧
    Real.Gamma (t + 1 / 2) ≤ Real.sqrt (2 * Real.pi) * Real.exp (t * Real.log t - t) := by sorry
