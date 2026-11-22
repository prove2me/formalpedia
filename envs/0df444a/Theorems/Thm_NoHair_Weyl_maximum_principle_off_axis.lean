-- Prove2me | Theorems.Thm_NoHair_Weyl_maximum_principle_off_axis
-- name    : NoHair.Weyl.maximum_principle_off_axis
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:02:10.606797+00:00
-- url     : https://prove2.me/theorems/9e005420-e10a-47e4-bf0b-7f9a79cbe7da
-- title:
--   Maximum principle off the rotation axis in logarithmic Weyl coordinates
-- statement:
--   Let $f(s,z)$ be a twice continuously differentiable real function, where $\rho=e^s$ is cylindrical radius. Suppose that $f$ is bounded above and is axisymmetrically subharmonic,
--   $$
--   f_{ss}+e^{2s}f_{zz}\ge0.
--   $$
--   For each $\varepsilon>0$, suppose $f\le\varepsilon$ whenever $\rho^2+z^2$ is sufficiently large. Then
--   $$
--   f(s,z)\le0\qquad\text{for every }(s,z).
--   $$
--   The uniform upper bound controls approach to the excluded axis $\rho=0$. No boundary value on that axis is prescribed.
-- source:
--   P. T. Chruściel, Y. Li and G. Weinstein, Mass and angular-momentum inequalities for axi-symmetric initial data sets. II. Angular momentum, Appendix C, Proposition C.4, eqs. (C.4)–(C.8), pp. 28–29, https://arxiv.org/abs/0712.4064. This is the classical axisymmetric upper-bound form. See also Chruściel, Costa and Heusler, Prop. 8.1, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_vacuumErnst

namespace NoHair.Weyl

theorem maximum_principle_off_axis (f : OrbitPoint → ℝ)
    (hf : ContDiff ℝ 2 f) (hsub : ∀ p, 0 ≤ scaledLaplacian f p)
    (hbound : ∃ C : ℝ, ∀ p, f p ≤ C)
    (hdecay : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ p : OrbitPoint,
      R ≤ Real.exp (2 * p.1) + p.2 ^ 2 → f p ≤ ε) :
    ∀ p, f p ≤ 0 := by
  sorry

end NoHair.Weyl
