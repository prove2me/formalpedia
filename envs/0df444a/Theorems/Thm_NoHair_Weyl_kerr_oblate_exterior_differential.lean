-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_oblate_exterior_differential
-- name    : NoHair.Weyl.kerr_oblate_exterior_differential
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:26:25.96469+00:00
-- url     : https://prove2.me/theorems/7b5d1db4-530a-4b2c-b991-c45077ea902a
-- title:
--   Radius and differential in oblate Kerr–Schild coordinates
-- statement:
--   At an off-axis point $(t,x,y,Z)$ of the Kerr exterior the Kerr–Schild radial function $r$ is smooth. With $c=Z/r$ one has $r>0$, $1-c^2>0$, $\Delta>0$, and
--   $$
--   x^2+y^2=(r^2+a^2)(1-c^2),\qquad
--   (r^2+a^2c^2)\,dr=r(x\,dx+y\,dy)+(r^2+a^2)c\,dZ.
--   $$
--   The differential formula evaluates on every tangent vector and includes extremal parameters.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

open scoped ContDiff

namespace NoHair.Weyl

theorem kerr_oblate_exterior_differential (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (y : E4) (hy : y ∈ offAxisExterior m a) :
    let r := ksRadius a y
    let c := y 3/r
    0 < r ∧ 0 < 1-c^2 ∧ 0 < kerrDelta m a r ∧
    y 1^2+y 2^2=(r^2+a^2)*(1-c^2) ∧ ContDiffAt ℝ ∞ (ksRadius a) y ∧
    ∀ v : E4, (r^2+a^2*c^2)*(fderiv ℝ (ksRadius a) y v) =
      r*(y 1*v 1+y 2*v 2)+(r^2+a^2)*c*v 3 := by
  sorry

end NoHair.Weyl
