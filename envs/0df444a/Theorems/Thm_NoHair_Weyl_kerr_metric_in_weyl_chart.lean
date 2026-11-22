-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_metric_in_weyl_chart
-- name    : NoHair.Weyl.kerr_metric_in_weyl_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:20:43.230574+00:00
-- url     : https://prove2.me/theorems/37aec783-48b2-49ba-b610-a5a57d59fb11
-- title:
--   Kerr–Schild metric coefficients in each normalized Weyl chart
-- statement:
--   In a normalized Boyer–Lindquist–Weyl chart $(t,\varphi,\rho,z)$ on the Kerr exterior off the axis, the pullback of
--   $$
--   -\rho^2X^{-1}dt^2+X(d\varphi+W\,dt)^2+(H/X)(d\rho^2+dz^2)
--   $$
--   equals the explicit vacuum Kerr–Schild coefficient matrix in Cartesian coordinates. Here $W$ and $H$ are the algebraic Kerr functions, before any radial integration.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylCoefficients

open Set

namespace NoHair.Weyl

theorem kerr_metric_in_weyl_chart (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0)
    (V : Set E4) (C : E4 → E4) (hc : IsKerrWeylChart m a V C) :
    ∀ y ∈ V, kerrNewmanMetric m a 0 y = kerrWeylMatrix m a C y := by
  sorry

end NoHair.Weyl
