-- Prove2me | Theorems.Thm_MaxwellWiki_continuity_equation
-- name    : MaxwellWiki.continuity_equation
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:05:08.014054+00:00
-- url     : https://prove2.me/theorems/010a9ad2-52cf-4381-b628-b3b2262098ff
-- title:
--   Continuity equation $\partial_t\rho+\nabla\cdot\mathbf J=0$ from Maxwell's equations
-- statement:
--   **Charge conservation (differential form).** Let $\varepsilon_0>0$ and $\mu_0>0$. Let $\mathbf E,\mathbf B,\mathbf J:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$ and $\rho:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ satisfy Maxwell's microscopic equations in SI units at every time and point,
--   $$\nabla\cdot\mathbf E=\frac{\rho}{\varepsilon_0},\qquad \nabla\cdot\mathbf B=0,\qquad \nabla\times\mathbf E=-\frac{\partial\mathbf B}{\partial t},\qquad \nabla\times\mathbf B=\mu_0\Big(\mathbf J+\varepsilon_0\frac{\partial\mathbf E}{\partial t}\Big),$$
--   and assume $\mathbf E$ and $\mathbf B$ are $C^2$ jointly in $(t,x)$. Then for every $t$ and $x$,
--   $$\frac{\partial\rho}{\partial t}+\nabla\cdot\mathbf J=0 .$$
--
--   This is the continuity equation the article derives "as a corollary of Maxwell's equations"; it expresses local conservation of electric charge.
--
--   **Formalization Note** No regularity is assumed on $\rho$ and $\mathbf J$: they are determined by $\mathbf E$ and $\mathbf B$ through Gauss's law and the Ampère–Maxwell law. The $C^2$ assumption on $\mathbf E,\mathbf B$ makes explicit the smoothness the article leaves implicit.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Charge conservation" (pp. 8–9 of the snapshot): the displayed chain $0=\nabla\cdot(\nabla\times\mathbf B)=\dots=\mu_0(\nabla\cdot\mathbf J+\partial\rho/\partial t)$, "i.e., $\partial\rho/\partial t+\nabla\cdot\mathbf J=0$"; Maxwell's equations as in section "Summary — Microscopic version in SI units" (p. 2).

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace MaxwellWiki

theorem continuity_equation (ε₀ μ₀ : ℝ) (hε₀ : 0 < ε₀) (hμ₀ : 0 < μ₀)
    (E B J : ℝ → Vec3 → Vec3) (ρ : ℝ → Vec3 → ℝ)
    (hE : ContDiff ℝ 2 (Function.uncurry E)) (hB : ContDiff ℝ 2 (Function.uncurry B))
    (hM : IsMaxwellSolution ε₀ μ₀ E B J ρ) (t : ℝ) (x : Vec3) :
    timeDeriv ρ t x + div (J t) x = 0 := by sorry

end MaxwellWiki
