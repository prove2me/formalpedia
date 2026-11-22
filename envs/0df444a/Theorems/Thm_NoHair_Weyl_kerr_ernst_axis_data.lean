-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_ernst_axis_data
-- name    : NoHair.Weyl.kerr_ernst_axis_data
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:22:42.601807+00:00
-- url     : https://prove2.me/theorems/99560a05-e03a-4124-9675-8e80c5f19ae2
-- title:
--   Axis and horizon limits of the Kerr norm and twist
-- statement:
--   Fix $m>0$ and $a$, and take $\ell\ge0$ satisfying $\ell^2=m^2-a^2$. For the Kerr Ernst pair in the convention $\partial_\rho w=\rho\,\partial_zY/X^2$, the two pieces of the exterior rotation axis have limits
--   $$
--   (X,Y)\longrightarrow (0,4ma)\quad(z>\ell),\qquad
--   (X,Y)\longrightarrow (0,-4ma)\quad(z<-\ell)
--   $$
--   as $\rho\downarrow0$ at fixed $z$. On the interior of a horizon interval of positive length, $|z|<\ell$, the axial norm has a strictly positive limit. The limiting twist jump is $8J$ with $J=ma$.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_ernst_axis_data (m a ℓ : ℝ) (hm : 0 < m) (hℓ : 0 ≤ ℓ)
    (hmatch : m^2 - a^2 = ℓ^2) :
    HasAxisData (kerrErnst m a) ℓ (m*a) := by
  sorry

end NoHair.Weyl
