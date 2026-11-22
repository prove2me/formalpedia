-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_boundary_profile_estimates
-- name    : NoHair.Weyl.kerr_boundary_profile_estimates
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:47:38.119544+00:00
-- url     : https://prove2.me/theorems/a35b7de1-6e32-43da-a003-0086cc1c1bd6
-- title:
--   Uniform axial norm and twist estimates for Kerr relative to its horizon interval
-- statement:
--   Write $r=m+u$, $c=z/u$, and take $\ell=\sqrt{m^2-a^2}$ and $J=ma$. For $A=(1-c^2)r^2$ and $Y_0=2J(3c-c^3)$ the Kerr Ernst potentials satisfy
--   $$
--   0\le X_K/A-1\le 3a^2/r^2,\qquad |(Y_K-Y_0)/A|\le 2m|a|^3/r^4 .
--   $$
--   Both estimates are uniform in the angle. In particular they imply the stated two-sided bounds at finite distance and uniform decay of the normalized errors at spatial infinity, also for extremal Kerr.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_weylBoundaryProfile

namespace NoHair.Weyl

theorem kerr_boundary_profile_estimates (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    let ℓ := Real.sqrt (m^2-a^2)
    let b := rodBoundaryProfile m ℓ (m*a)
    let K := kerrErnst m a
    HasProfileEstimates K b ∧ ∀ p,
      let r := m+prolateRadius ℓ p
      let x := K.normSq p / b.normSq p - 1
      let y := (K.twist p - b.twist p) / b.normSq p
      0 < b.normSq p ∧ 0 ≤ x ∧ x ≤ 3*a^2/r^2 ∧ |y| ≤ 2*m*|a|^3/r^4 := by
  sorry

end NoHair.Weyl
