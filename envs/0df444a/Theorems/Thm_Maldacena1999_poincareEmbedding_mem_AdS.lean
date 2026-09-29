-- Prove2me | Theorems.Thm_Maldacena1999_poincareEmbedding_mem_AdS
-- name    : Maldacena1999.poincareEmbedding_mem_AdS
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T17:04:25.424669+00:00
-- url     : https://prove2.me/theorems/bb6acb82-2da7-4857-82f2-b878dd1534f2
-- title:
--   Poincaré coordinates land on the $\mathrm{AdS}_{p+2}$ hyperboloid
-- statement:
--   Let $p\ge0$, $R>0$, $U>0$ and $x=(x_0,\dots,x_p)\in\mathbb R^{1,p}$. Define $V=\dfrac{x^2U}{R^2}+\dfrac{R^2}{U}$, where $x^2=-x_0^2+x_1^2+\cdots+x_p^2$, and the point $X\in\mathbb R^{2,p+1}$ by
--   $$X_{-1}=\frac{U+V}{2},\qquad X_{p+1}=\frac{U-V}{2},\qquad X_\alpha=\frac{x_\alpha U}{R}\ (\alpha=0,\dots,p).$$
--   Then $X$ lies on the anti-de Sitter hyperboloid of radius $R$:
--   $$-X_{-1}^2-X_0^2+X_1^2+\cdots+X_p^2+X_{p+1}^2=-R^2 .$$
--
--   This shows that the coordinates $(U,x)$ of eq. (A.2), used throughout the paper, describe points of $\mathrm{AdS}_{p+2}$.
-- source:
--   J. Maldacena, The Large-N Limit of Superconformal Field Theories and Supergravity, Int. J. Theor. Phys. 38 (1999) 1113-1133, https://doi.org/10.1023/A:1026654312961 (arXiv:hep-th/9711200), Appendix, eqs. (A.1)-(A.2), p. 1130

import Mathlib
import Definitions.Def_Maldacena1999_Defs

open Filter Topology

namespace Maldacena1999

theorem poincareEmbedding_mem_AdS (p : ℕ) (R : ℝ) (hR : 0 < R)
    (U : ℝ) (hU : 0 < U) (x : Fin (p + 1) → ℝ) :
    poincareEmbedding p R (U, x) ∈ AdS p R := by
  sorry

end Maldacena1999
