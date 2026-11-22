-- Prove2me | Theorems.Thm_NoHair_Weyl_prolate_coordinate_differentials
-- name    : NoHair.Weyl.prolate_coordinate_differentials
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:15:45.975665+00:00
-- url     : https://prove2.me/theorems/0d4bd545-278a-4a0f-906e-60f00f6c8a51
-- title:
--   First differentials of the prolate orbit coordinates at any horizon length
-- statement:
--   In logarithmic Weyl coordinates set $w=e^{2s}$, $u$ equal to the mean focal distance, $c=z/u$, $A=u^2-k^2$, $B=1-c^2$, and $D=u^2-k^2c^2$. Then $u,B,D>0$, $w=AB$, and the smooth orbit coordinates satisfy
--   $$
--   u_s=wu/D,\quad u_z=cA/D,\quad c_s=-wc/D,\quad c_z=uB/D .
--   $$
--   The same formulas hold when the two foci coincide.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016. Chruściel, Costa and Heusler, §8.3.1, eqs. (8.17)–(8.18), https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_kerrWeylModel

namespace NoHair.Weyl

theorem prolate_coordinate_differentials (k : ℝ) :
    let U := prolateRadius k
    let C := fun p : OrbitPoint => p.2/U p
    ContDiff ℝ 2 U ∧ ContDiff ℝ 2 C ∧ ∀ p,
      let u := U p
      let c := C p
      let w := Real.exp (2*p.1)
      let A := u^2-k^2
      let B := 1-c^2
      let D := u^2-k^2*c^2
      0 < u ∧ 0 < B ∧ 0 < D ∧ w = A*B ∧
      ds U p = w*u/D ∧ dz U p = c*A/D ∧ ds C p = -w*c/D ∧ dz C p = u*B/D := by
  sorry

end NoHair.Weyl
