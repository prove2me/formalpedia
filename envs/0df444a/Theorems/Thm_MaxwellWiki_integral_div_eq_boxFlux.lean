-- Prove2me | Theorems.Thm_MaxwellWiki_integral_div_eq_boxFlux
-- name    : MaxwellWiki.integral_div_eq_boxFlux
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T20:04:11.943933+00:00
-- url     : https://prove2.me/theorems/66ce9b9b-86b3-4fa3-963e-dd22685b280e
-- title:
--   Gauss divergence theorem on a box: $\iiint_\Omega\nabla\cdot F\,dV=\oint_{\partial\Omega}F\cdot d\mathbf S$
-- statement:
--   **Gauss divergence theorem on a rectangular box.** Let $a\le b$ in $\mathbb{R}^3$ (coordinatewise), let $\Omega=[a_0,b_0]\times[a_1,b_1]\times[a_2,b_2]$, and let $F:\mathbb{R}^3\to\mathbb{R}^3$ be a $C^1$ vector field. Then
--   $$\iiint_{\Omega}\nabla\cdot F\,dV=\oint_{\partial\Omega}F\cdot d\mathbf S=\sum_{i=0}^{2}\Big(\int_{\text{face }x_i=b_i}F_i\,dA-\int_{\text{face }x_i=a_i}F_i\,dA\Big).$$
--
--   The article uses the divergence theorem both to relate the integral and differential forms of Gauss's laws and, in the *Charge conservation* section, to pass from $\partial_t\rho+\nabla\cdot\mathbf J=0$ to the statement about charge in a fixed volume.
--
--   **Formalization Note** The article's volume $\Omega$ is arbitrary with closed boundary; this statement is the special case of a rectangular box, where the outward flux is the explicit sum of face integrals defined in the shared definition file.
-- source:
--   Wikipedia, "Maxwell's equations", https://en.wikipedia.org/wiki/Maxwell%27s_equations (24-page PDF snapshot supplied by the proposer), section "Relationship between differential and integral formulations — Flux and divergence" (p. 7 of the snapshot) and section "Charge conservation" (p. 9): "By the Gauss divergence theorem, this means ..."

import Mathlib
import Definitions.Def_MaxwellWiki_Defs

open MaxwellWiki

namespace MaxwellWiki

theorem integral_div_eq_boxFlux (F : Vec3 → Vec3) (hF : ContDiff ℝ 1 F) (a b : Vec3)
    (hab : a ≤ b) :
    ∫ x in Set.Icc a b, div F x = boxFlux F a b := by sorry

end MaxwellWiki
