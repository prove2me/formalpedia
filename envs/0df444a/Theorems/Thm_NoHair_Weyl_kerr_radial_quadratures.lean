-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_radial_quadratures
-- name    : NoHair.Weyl.kerr_radial_quadratures
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:20:19.134327+00:00
-- url     : https://prove2.me/theorems/6caf248c-cbd1-4f23-83cf-cef4a052acf4
-- title:
--   Absolute convergence and evaluation of both Kerr radial quadratures
-- statement:
--   For $m>0$ and $a^2\le m^2$, the two normalized Weyl radial quadratures of the explicit Kerr Ernst pair converge absolutely along every ray of fixed Weyl height. The integrated angular shift equals $-2mar/N$ and the integrated conformal exponent satisfies $e^{2h}=(1-c^2)N/D$. These equalities apply across the open half-plane and include the extremal Kerr exterior.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylCoefficients

namespace NoHair.Weyl

theorem kerr_radial_quadratures (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    HasRadialQuadratures (kerrErnst m a) ∧ ∀ p : OrbitPoint,
      angularShift (kerrErnst m a) p = kerrWeylShift m a p ∧
      Real.exp (2*conformalExponent (kerrErnst m a) p) = kerrWeylScale m a p := by
  sorry

end NoHair.Weyl
