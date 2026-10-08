-- Prove2me | Theorems.Thm_OptInapprox_Orthant_eq_19_20
-- name    : OptInapprox.Orthant.eq_19_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:32.45398+00:00
-- url     : https://prove2.me/theorems/567a1bdb-3f55-4183-b566-6a424b22fee0
-- title:
--   (19)–(20), proof of Proposition 6.1, p. 31 — ∫∫exp(−g) ≤ ∫∫exp(−h) = √(2π)(1 + ρ)√(1 − ρ²)·t·exp(((1 − ρ)/(1 + ρ))·t²/2)·N(t√((1 − ρ)/(1 + ρ)))
-- statement:
--   Let $\phi$ be the standard Gaussian density and $N(x)=\int_x^\infty\phi$. Let $0\le\rho<1$ and $t>0$, and let $g,h$ be the exponents
--   $$g(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2+2(1-\rho)uv}{2(1-\rho^2)t^2},\qquad h(u,v)=\frac{u+v}{1+\rho}+\frac{(u-v)^2}{2(1-\rho^2)t^2}.$$
--   Then:
--
--   1. $\exp(-h)$ is integrable on the quadrant $(0,\infty)^2$;
--   2. (19) $\displaystyle\int_0^\infty\!\!\int_0^\infty \exp(-g(u,v))\,du\,dv\ \le\ \int_0^\infty\!\!\int_0^\infty \exp(-h(u,v))\,du\,dv$;
--   3. (20)
--   $$\int_0^\infty\!\!\int_0^\infty \exp(-h(u,v))\,du\,dv=\sqrt{2\pi}\,(1+\rho)\sqrt{1-\rho^2}\cdot t\cdot\exp\!\Big(\frac{1-\rho}{1+\rho}\cdot\frac{t^2}{2}\Big)\cdot N\!\Big(t\sqrt{\tfrac{1-\rho}{1+\rho}}\Big).$$
--
--   Combined with (18), this gives Proposition 6.1 for $0\le\rho<1$: the exponential factors cancel to $e^{-t^2/2}$ and the constants to $(1+\rho)/(\sqrt{2\pi}\,t)$.
--
--   **Formalization Note** The integrals are iterated Bochner integrals over $(0,\infty)$, inner variable $u$. Since a Bochner integral of a non-integrable function is $0$ in Lean, part 1 records that the right-hand side of (19) is a genuine integral; it is part of the conclusion, not a hypothesis. The hypothesis $\rho<1$ is the range in which $g$, $h$ and the right-hand side of (20) are defined.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), p. 31, proof of Proposition 6.1, displays (19) and (20)

import Mathlib
import Definitions.Def_OptInapprox_Orthant_Setting

open MeasureTheory ProbabilityTheory

namespace OptInapprox.Orthant

/-- (19)–(20), proof of Proposition 6.1, p. 31. -/
theorem eq_19_20 (t ρ : ℝ) (ht : 0 < t) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    IntegrableOn (fun p : ℝ × ℝ => Real.exp (-hExp ρ t p.1 p.2))
        (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ)) ∧
      (∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ), Real.exp (-gExp ρ t u v)) ≤
        ∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ), Real.exp (-hExp ρ t u v) ∧
      (∫ v in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ), Real.exp (-hExp ρ t u v)) =
        Real.sqrt (2 * Real.pi) * (1 + ρ) * Real.sqrt (1 - ρ ^ 2) * t *
          Real.exp ((1 - ρ) / (1 + ρ) * (t ^ 2 / 2)) *
          tailN (t * Real.sqrt ((1 - ρ) / (1 + ρ))) := by sorry

end OptInapprox.Orthant
