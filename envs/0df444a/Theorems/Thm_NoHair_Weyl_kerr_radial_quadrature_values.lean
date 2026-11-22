-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_radial_quadrature_values
-- name    : NoHair.Weyl.kerr_radial_quadrature_values
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:14:50.650366+00:00
-- url     : https://prove2.me/theorems/5392f137-5913-4546-ae61-ce42db75707f
-- title:
--   Values of the two normalized Kerr radial quadratures
-- statement:
--   For an admissible vacuum Kerr solution, both radial integrals defining its Weyl angular shift and conformal exponent converge absolutely. Write $k=\sqrt{m^2-a^2}$, $x$ for the mean of the distances to the rod endpoints, $r=m+x$, $c=z/x$, $B=1-c^2$, $D=x^2-k^2c^2$ and $P=(r^2+a^2)^2-a^2\Delta B$. In the normalization at spatial infinity their values are
--
--   $$ w=-\frac{2mra}{P},\qquad e^{2h}=\frac{BP}{D}. $$
--
--   These are identities throughout the open Weyl half-plane, including the parameter case $a^2=m^2$.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein's equations, Appendix A, equations (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, https://arxiv.org/abs/0806.0016. The constants of the primitives use the mission's radial-ray normalization.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_radial_quadrature_values (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    HasRadialQuadratures (kerrErnst m a) ∧ ∀ p : OrbitPoint,
      let k := Real.sqrt (m^2-a^2)
      let x := prolateRadius k p
      let r := m+x
      let c := p.2/x
      let B := 1-c^2
      let P := (r^2+a^2)^2-a^2*kerrDelta m a r*B
      let D := x^2-k^2*c^2
      angularShift (kerrErnst m a) p = -(2*m*r*a)/P ∧
      Real.exp (2*conformalExponent (kerrErnst m a) p) = B*P/D := by
  sorry

end NoHair.Weyl
