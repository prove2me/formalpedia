-- Prove2me | Theorems.Thm_OptInapprox_Orthant_lower_bound
-- name    : OptInapprox.Orthant.lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:27.636341+00:00
-- url     : https://prove2.me/theorems/ae9d0a57-9eed-458b-8d10-5343b0010ba5
-- title:
--   Proof of Corollary 10, p. 31 — side note: μ·N(t√((1 − ρ)/(1 + ρ))) is a lower bound on Λ_ρ(μ)
-- statement:
--   Let $\phi$ be the standard Gaussian density and $N(x)=\int_x^\infty\phi$. Let $0\le\rho\le1$, let $t>0$ and let $\mu=N(t)$, so $0\le\mu<1/2$. Let $\Lambda_\rho(\mu)=\Pr[X\ge t,\ X'\ge t]$ with $X$ standard Gaussian and $X'=\rho X+\sqrt{1-\rho^2}\,Y$, $Y$ an independent standard Gaussian. Then
--   $$\mu\cdot N\!\Big(t\sqrt{\tfrac{1-\rho}{1+\rho}}\Big)\ \le\ \Lambda_\rho(\mu).$$
--
--   Together with Proposition 6.1 this pins $\Lambda_\rho(\mu)$ between $\mu\,N(t\sqrt{(1-\rho)/(1+\rho)})$ and $(1+\rho)\frac{\phi(t)}{t}N(t\sqrt{(1-\rho)/(1+\rho)})$; since $\phi(t)/t\sim N(t)=\mu$ as $t\to\infty$, the two bounds differ by at most the factor $1+\rho$ asymptotically.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 31, proof of Corollary 10 (side note)

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting

open MeasureTheory ProbabilityTheory

namespace OptInapprox.Orthant

/-- Proof of Corollary 10, p. 31 (side note): `μ · N(t√((1-ρ)/(1+ρ)))` is a lower bound on `Λ_ρ(μ)`. -/
theorem lower_bound (μ t ρ : ℝ) (hμ : 0 ≤ μ ∧ μ < 1 / 2) (ht : 0 < t) (hNt : tailN t = μ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    μ * tailN (t * Real.sqrt ((1 - ρ) / (1 + ρ))) ≤ Lambda ρ μ := by sorry

end OptInapprox.Orthant
