-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_chart_reconstruction
-- name    : NoHair.Weyl.kerr_chart_reconstruction
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:28:09.031786+00:00
-- url     : https://prove2.me/theorems/1c5aac89-08f7-48c5-bdf9-3f38f9602c25
-- title:
--   Reconstruction of the Kerr metric in normalized local Weyl charts
-- statement:
--   For each Kerr black hole with $m>0$ and $a^2\le m^2$, show that its explicit axial norm and twist have convergent normalized radial quadratures. The resulting Weyl–Papapetrou metric reconstructs the Kerr–Schild coefficients in every normalized local Weyl chart. Its coefficients in Kerr–Schild coordinates are continuous on the exterior, and every off-axis point of that exterior belongs to such a chart. This includes the extremal exterior.
--
--   Let $k^2=m^2-a^2$, $c=\cos\theta$, $u=r-m$, $\Sigma=r^2+a^2 c^2$, and $D=u^2-k^2c^2$. In the normalization used here the candidate angular shift and conformal exponent are
--   $$
--   w_K=-\frac{2mar(1-c^2)}{\Sigma X},\qquad e^{2h_K}=\frac{X\Sigma}{D}.
--   $$
--   Differentiation at fixed Weyl height yields the radial quadrature rates for $w_K$ and $h_K-s$, with $s=\log\rho$. For the normalization at infinity one can use $t=e^{-s}$. At fixed $z$,
--   $$
--   t u=\tfrac12\left(\sqrt{1+t^2(z-k)^2}+\sqrt{1+t^2(z+k)^2}\right).
--   $$
--   It extends smoothly to $t=0$ with value $1$. In the compactified variable $w_K$ and $h_K-s$ extend smoothly with value zero, so their radial derivatives have integrable tails. Metric reconstruction also requires the normalized Boyer–Lindquist chart differentials specified in the formal statement.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_chart_reconstruction (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    IsWeylRepresentation m a (kerrNewmanMetric m a 0) (kerrErnst m a) ∧
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  sorry

end NoHair.Weyl
