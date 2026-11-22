-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_reduced_field_equations
-- name    : NoHair.Weyl.kerr_reduced_field_equations
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:27:49.152802+00:00
-- url     : https://prove2.me/theorems/4ff30341-4b46-43c8-9f13-bf9b3114a071
-- title:
--   Vacuum Ernst differential identities for the explicit Kerr potentials
-- statement:
--   For the axial norm $X$ and twist $Y$ of the explicit Kerr pair with $m>0$ and $a^2\le m^2$, verify on the open Weyl half-plane that
--   $$
--   X L X=\langle \nabla X,\nabla X\rangle_s-\langle\nabla Y,\nabla Y\rangle_s,
--   \qquad X L Y=2\langle\nabla X,\nabla Y\rangle_s .
--   $$
--   Here $s=\log\rho$, $L f=f_{ss}+e^{2s}f_{zz}$, and $\langle\nabla f,\nabla g\rangle_s=f_sg_s+e^{2s}f_zg_z$. Both potentials are specified by explicit rational expressions in the Boyer–Lindquist radius and polar cosine.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem kerr_reduced_field_equations (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ p : OrbitPoint,
      let v := kerrErnst m a
      v.normSq p * scaledLaplacian v.normSq p =
        scaledGradientPair v.normSq v.normSq p - scaledGradientPair v.twist v.twist p ∧
      v.normSq p * scaledLaplacian v.twist p = 2*scaledGradientPair v.normSq v.twist p := by
  sorry

end NoHair.Weyl
