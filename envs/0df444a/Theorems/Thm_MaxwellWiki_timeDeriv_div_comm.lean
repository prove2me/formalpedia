-- Prove2me | Theorems.Thm_MaxwellWiki_timeDeriv_div_comm
-- name    : MaxwellWiki.timeDeriv_div_comm
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:02:49.173049+00:00
-- url     : https://prove2.me/theorems/7c0c8746-df88-4d08-8e52-81384d47095a
-- title:
--   Interchanging derivatives: $\partial_t(\nabla\cdot F)=\nabla\cdot(\partial_t F)$
-- statement:
--   **Interchanging time and space derivatives.** Let $F:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}^3$, $(t,x)\mapsto F(t,x)$, be of class $C^2$ jointly in $(t,x)$. Then for all $t\in\mathbb{R}$ and $x\in\mathbb{R}^3$,
--   $$\frac{\partial}{\partial t}\big(\nabla\cdot F(t,\cdot)\big)(x)=\nabla\cdot\Big(\frac{\partial F}{\partial t}(t,\cdot)\Big)(x).$$
--
--   This is the "interchanging derivatives" step of the *Charge conservation* section, applied there to $F=\mathbf E$ to turn $\nabla\cdot(\varepsilon_0\,\partial_t\mathbf E)$ into $\varepsilon_0\,\partial_t(\nabla\cdot\mathbf E)$.
--
--   **Formalization Note** Joint $C^2$ regularity in $(t,x)$ is assumed; the article leaves the needed smoothness implicit.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Charge conservation" (p. 8 of the snapshot): "Expanding the divergence of the right-hand side, interchanging derivatives, and applying Gauss's law gives ..."

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace MaxwellWiki

theorem timeDeriv_div_comm (F : ℝ → Vec3 → Vec3) (hF : ContDiff ℝ 2 (Function.uncurry F))
    (t : ℝ) (x : Vec3) :
    timeDeriv (fun s y => div (F s) y) t x = div (fun y => timeDeriv F t y) x := by sorry

end MaxwellWiki
