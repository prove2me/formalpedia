-- Prove2me | Theorems.Thm_NoHair_Weyl_kerr_parameters_from_rod_and_spin
-- name    : NoHair.Weyl.kerr_parameters_from_rod_and_spin
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T21:19:25.223793+00:00
-- url     : https://prove2.me/theorems/a34b3d37-03ee-44db-9e73-73a91095a625
-- title:
--   Kerr mass and spin from horizon interval length and angular momentum
-- statement:
--   Let $\ell\ge0$ be the half-length of a connected horizon interval in Weyl coordinates and let $J$ be its angular momentum. Assume $\ell>0$ or $J\ne0$. There is exactly one pair $(m,a)$ satisfying
--   $$
--   m>0,\qquad m^2-a^2=\ell^2,\qquad ma=J.
--   $$
--   The two equations match a comparison Kerr metric to the prescribed interval and spin. They include both a point horizon with nonzero angular momentum and a positive-length horizon with zero angular momentum.
-- source:
--   P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, proof of Corollary 6.3, pp. 51–52, https://arxiv.org/abs/0806.0016. S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, eqs. (90)–(95), https://arxiv.org/abs/gr-qc/0508061.

import Mathlib.Data.Real.Sqrt

namespace NoHair.Weyl

theorem kerr_parameters_from_rod_and_spin (ℓ J : ℝ) (hℓ : 0 ≤ ℓ)
    (hn : 0 < ℓ ∨ J ≠ 0) :
    ∃! q : ℝ × ℝ, 0 < q.1 ∧ q.1 ^ 2 - q.2 ^ 2 = ℓ ^ 2 ∧ q.1 * q.2 = J := by
  sorry

end NoHair.Weyl
