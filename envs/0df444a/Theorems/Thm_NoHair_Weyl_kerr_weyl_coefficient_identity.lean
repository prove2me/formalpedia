-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_weyl_coefficient_identity
-- name    : NoHair.Weyl.kerr_weyl_coefficient_identity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:14:43.263622+00:00
-- url     : https://prove2.me/theorems/f71dd223-45ec-4af4-a6b2-a8f3dd09f5a5
-- title:
--   Kerr–Schild metric coefficients in a normalized Weyl chart
-- statement:
--   Consider any of the specified off-axis Weyl charts for Kerr. At a point in its domain put $x=r-m$, $c=\cos\theta$, $B=1-c^2$, $k^2=m^2-a^2$, $D=x^2-k^2c^2$ and $P=(r^2+a^2)^2-a^2\Delta B$. If the angular shift and conformal coefficient at the corresponding Weyl point have their values $-2mra/P$ and $BP/D$, respectively, the Weyl–Papapetrou metric transformed by the chart differential agrees, coefficient by coefficient, with the Kerr–Schild metric. The two scalar hypotheses allow the independent integral evaluation to be used directly.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, equations (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein's equations, Appendix A, equations (90)–(94), https://arxiv.org/abs/gr-qc/0508061.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_weyl_coefficient_identity (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (V : Set E4) (coord : E4 → E4) (hc : IsKerrWeylChart m a V coord) (y : E4) (hy : y ∈ V) :
    let p : OrbitPoint := (Real.log ((coord y) 2), (coord y) 3)
    let k := Real.sqrt (m^2-a^2)
    let x := prolateRadius k p
    let r := m+x
    let c := p.2/x
    let B := 1-c^2
    let P := (r^2+a^2)^2-a^2*kerrDelta m a r*B
    let D := x^2-k^2*c^2
    angularShift (kerrErnst m a) p = -(2*m*r*a)/P →
    Real.exp (2*conformalExponent (kerrErnst m a) p) = B*P/D →
    kerrNewmanMetric m a 0 y = metricInChart (kerrErnst m a) coord y := by
  sorry

end NoHair.Weyl
