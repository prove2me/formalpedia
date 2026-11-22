-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_radial_rate_identities
-- name    : NoHair.Weyl.kerr_radial_rate_identities
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:20:14.300949+00:00
-- url     : https://prove2.me/theorems/2491a8ff-c9ac-4db3-b088-dba6ac70253c
-- title:
--   Differential quadrature identities for the Kerr shift and conformal exponent
-- statement:
--   Let $W$ and $H$ denote the explicit Kerr Weyl shift and positive conformal scale, and let $(X,Y)$ be the axial norm and twist. For a ray of fixed Weyl height $z$ and $s=\log\rho$, the derivatives satisfy
--   $$
--   W_s=e^{2s}Y_z/X^2,\qquad
--   (\tfrac12\log H-s)_s=
--   \frac{X_s^2+Y_s^2-e^{2s}(X_z^2+Y_z^2)}{4X^2}-1.
--   $$
--   Verify the identities for all subextremal and extremal Kerr black holes.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016.

import Definitions.Def_NoHair_kerrWeylCoefficients

namespace NoHair.Weyl

theorem kerr_radial_rate_identities (m a : ℝ) (hm : IsKerrNewmanBlackHoleParams m a 0) :
    ∀ s z : ℝ, 0 < kerrWeylScale m a (s,z) ∧
      HasDerivAt (fun t => kerrWeylShift m a (t,z)) (shiftRate (kerrErnst m a) (s,z)) s ∧
      HasDerivAt (fun t => Real.log (kerrWeylScale m a (t,z))/2-t)
        (conformalRate (kerrErnst m a) (s,z)) s := by
  sorry

end NoHair.Weyl
