-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_weyl_model
-- name    : NoHair.Weyl.kerr_weyl_model
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:22:49.833704+00:00
-- url     : https://prove2.me/theorems/617fecf3-f895-4ec5-8602-32f5868c5558
-- title:
--   The explicit Kerr metric and Ernst equations in normalized Weyl charts
-- statement:
--   Let $m>0$ and $a^2\le m^2$. The explicit axial norm and twist of the Kerr metric solve the vacuum Ernst equations on the open Weyl half-plane. Their two normalized radial quadratures converge and reconstruct the Kerr metric in every normalized Weyl chart,
--   $$
--   g_K=-\frac{\rho^2}{X}\,dt^2+X(d\varphi+w\,dt)^2+\frac{e^{2h}}{X}(d\rho^2+dz^2).
--   $$
--   These charts cover the part of the Kerr exterior off the rotation axis. That part is dense, and the Kerr–Schild coefficients are continuous on the entire exterior. This statement concerns only the explicit Kerr family, including $|a|=m$.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_weyl_model (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    (kerrErnst m a).IsSolution ∧
    IsWeylRepresentation m a (kerrNewmanMetric m a 0) (kerrErnst m a) ∧
    kerrNewmanDOC m a 0 ⊆ closure (offAxisExterior m a) ∧
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  sorry

end NoHair.Weyl
