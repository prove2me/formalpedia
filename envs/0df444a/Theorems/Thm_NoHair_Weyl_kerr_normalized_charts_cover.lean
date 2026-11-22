-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_normalized_charts_cover
-- name    : NoHair.Weyl.kerr_normalized_charts_cover
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T22:16:07.070934+00:00
-- url     : https://prove2.me/theorems/14557211-8ec0-40a5-b693-4b2d16f2e700
-- title:
--   Normalized Weyl charts cover the off-axis Kerr exterior
-- statement:
--   Every point outside the outer Kerr horizon and off the rotation axis has a neighborhood with smooth coordinates $(t_{\rm BL},\varphi_{\rm BL},\rho,z)$, with smooth local inverse. The first two differentials have the normalized Boyer–Lindquist form in Kerr–Schild coordinates, while $\rho=\sqrt{\Delta}\sin\theta$ and $z=(r-m)\cos\theta$. This includes $a^2=m^2$ on the open exterior.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_normalized_charts_cover (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ y ∈ offAxisExterior m a, ∃ V C, y ∈ V ∧ IsKerrWeylChart m a V C := by
  sorry

end NoHair.Weyl
