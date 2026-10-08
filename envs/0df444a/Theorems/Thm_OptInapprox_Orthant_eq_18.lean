-- Prove2me | Theorems.Thm_OptInapprox_Orthant_eq_18
-- name    : OptInapprox.Orthant.eq_18
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:27.680982+00:00
-- url     : https://prove2.me/theorems/99ed9b42-5140-4489-8073-d48dabe62364
-- title:
--   (18), proof of Proposition 6.1, p. 30 — Λ_ρ(μ) as a double integral of exp(−g(u, v)) over the quadrant
-- statement:
--   Let $\phi$ be the standard Gaussian density and $N(x)=\int_x^\infty\phi$ its tail. Let $0\le\rho<1$, let $t>0$, and let $\mu=N(t)$ (so $0\le\mu<1/2$). Let $\Lambda_\rho(\mu)=\Pr[X\ge t,\ X'\ge t]$, where $X$ is standard Gaussian and $X'=\rho X+\sqrt{1-\rho^2}\,Y$ with $Y$ an independent standard Gaussian. With
--   $$g(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2+2(1-\rho)uv}{2(1-\rho^2)t^2},$$
--   we have
--   $$\Lambda_\rho(\mu)=\frac{1}{2\pi\sqrt{1-\rho^2}\cdot t^2}\exp\!\Big(-\frac{t^2}{1+\rho}\Big)\int_0^\infty\!\!\int_0^\infty \exp(-g(u,v))\,du\,dv .$$
--
--   This is the exact integral representation from which Proposition 6.1 is obtained by bounding $g$ from below; it rewrites the orthant probability in coordinates centred at the corner $(t,t)$ of the orthant and scaled by $1/t$.
--
--   **Formalization Note** The double integral is the iterated Bochner integral over $(0,\infty)$, inner variable $u$, outer variable $v$, as printed ($du\,dv$). The page does not restrict $\rho$ beyond Proposition 6.1's $0\le\rho\le1$; the hypothesis $\rho<1$ is added because the prefactor divides by $\sqrt{1-\rho^2}$, so (18) has no meaning at $\rho=1$ (in Lean the prefactor would become $0$ and the identity would be false).
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 30, proof of Proposition 6.1, display (18) (cited from the proof of Lemma 11.1 of de Klerk, Pasechnik & Warners [12])

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting

open MeasureTheory ProbabilityTheory

namespace OptInapprox.Orthant

/-- (18), proof of Proposition 6.1, p. 30. -/
theorem eq_18 (μ t ρ : ℝ) (hμ : 0 ≤ μ ∧ μ < 1 / 2) (ht : 0 < t) (hNt : tailN t = μ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Lambda ρ μ =
      (2 * Real.pi * Real.sqrt (1 - ρ ^ 2) * t ^ 2)⁻¹ * Real.exp (-t ^ 2 / (1 + ρ)) *
        ∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ), Real.exp (-gExp ρ t u v) := by sorry

end OptInapprox.Orthant
