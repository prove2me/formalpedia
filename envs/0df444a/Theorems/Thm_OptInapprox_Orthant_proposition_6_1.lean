-- Prove2me | Theorems.Thm_OptInapprox_Orthant_proposition_6_1
-- name    : OptInapprox.Orthant.proposition_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:27.314011+00:00
-- url     : https://prove2.me/theorems/8ab2d18d-3a6f-4939-984b-721670e58bf0
-- title:
--   Proposition 6.1, p. 14 — Λ_ρ(μ) ≤ (1 + ρ)·(φ(t)/t)·N(t√((1 − ρ)/(1 + ρ))) for 0 ≤ μ < 1/2, N(t) = μ, 0 ≤ ρ ≤ 1
-- statement:
--   Denote by $\phi$ the Gaussian density function $\phi(x)=\frac{1}{\sqrt{2\pi}}e^{-x^2/2}$, and let $N(x)=\int_x^\infty\phi$ be the Gaussian tail probability function. Let $X$ and $Y$ be independent standard Gaussians and, for $0\le\rho\le1$, let $X'=\rho X+\sqrt{1-\rho^2}\,Y$, so that $(X,X')$ is a centred normal pair with covariance matrix $\begin{pmatrix}1&\rho\\ \rho&1\end{pmatrix}$. For $\mu\in(0,1)$ let $\Lambda_\rho(\mu)=\Pr[X\ge t\text{ and }X'\ge t]$, where $t$ is chosen so that $\Pr[X\ge t]=\mu$ (Definition 8).
--
--   For any $0\le\mu<1/2$, let $t>0$ be the number such that $N(t)=\mu$. Then for all $0\le\rho\le1$,
--   $$\Lambda_\rho(\mu)\ \le\ (1+\rho)\cdot\frac{\phi(t)}{t}\cdot N\!\Big(t\sqrt{\tfrac{1-\rho}{1+\rho}}\Big).\tag{4}$$
--
--   Proposition 6.1 is the upper bound on the Gaussian noise stability of a threshold that the paper feeds into the MOO theorem to obtain its MAX-2LIN(q) and MAX-q-CUT hardness bounds; as $\mu\to0$ it is tight up to a factor $1+o(1)$ (Corollary 10).
--
--   **Formalization Note** The statement quantifies over $t>0$ and $\mu$ with $N(t)=\mu$, exactly as the page does; the page's hypothesis $0\le\mu<1/2$ is kept, although it follows from $t>0$ and $N(t)=\mu$ (and $\mu=0$ admits no such $t$). $\Lambda_\rho(\mu)$ is a probability under the product of two standard Gaussian laws, never the right-hand side of a formula. The case $\rho=1$ is included as on the page: there $X'=X$, $\Lambda_1(\mu)=\mu$, and (4) reads $N(t)\le\phi(t)/t$.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 14, Proposition 6.1, display (4); Λ_ρ(μ) from p. 9, Definition 8

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting

open MeasureTheory ProbabilityTheory

namespace OptInapprox.Orthant

/-- Proposition 6.1, p. 14. -/
theorem proposition_6_1 (μ t ρ : ℝ) (hμ : 0 ≤ μ ∧ μ < 1 / 2) (ht : 0 < t) (hNt : tailN t = μ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Lambda ρ μ ≤ (1 + ρ) * (phi t / t) * tailN (t * Real.sqrt ((1 - ρ) / (1 + ρ))) := by sorry

end OptInapprox.Orthant
