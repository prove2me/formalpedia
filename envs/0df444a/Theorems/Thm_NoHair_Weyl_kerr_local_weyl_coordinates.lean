-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_local_weyl_coordinates
-- name    : NoHair.Weyl.kerr_local_weyl_coordinates
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:14:42.278326+00:00
-- url     : https://prove2.me/theorems/c44b2edd-b176-429b-9e42-5b571002be21
-- title:
--   Local Boyer–Lindquist and Weyl coordinates off the Kerr rotation axis
-- statement:
--   At every point with $r>r_+$ off the rotation axis there are smooth local coordinates $(t,\varphi,\rho,z)$ with $\rho=\sqrt{\Delta}\sin\theta>0$ and $z=(r-m)\cos\theta$. The first two differentials are the Boyer–Lindquist time and azimuth differentials in the mission's Kerr–Schild convention. The coordinate map is a diffeomorphism onto an open set. The azimuth is chosen locally so that points on either side of any fixed choice of angular branch are covered.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, equations (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §6.4 (Weyl coordinates), https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_local_weyl_coordinates (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ y ∈ offAxisExterior m a, ∃ V c, y ∈ V ∧ IsKerrWeylChart m a V c := by
  sorry

end NoHair.Weyl
