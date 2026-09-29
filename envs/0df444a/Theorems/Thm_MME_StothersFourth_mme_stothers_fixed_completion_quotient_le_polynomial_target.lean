-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_completion_quotient_le_polynomial_target
-- name    : MME.StothersFourth.mme_stothers_fixed_completion_quotient_le_polynomial_target
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:54:36.418416+00:00
-- url     : https://prove2.me/theorems/0d9ab3eb-1a31-48ea-a178-5d531893b1d4
-- title:
--   Polynomial comparison of Stothers completion quotients
-- statement:
--   Let $k$ be any supported $45$-cell joint table having the fixed Stothers marginal in all three modes, at a positive scale $m$. Its fixed-mode completion quotient is bounded by the fixed target completion degree $D_*$ according to
--
--   $$
--   \frac{\prod_{j=0}^{8}M_j!}{\prod_{\sigma\in\Omega}k_\sigma!}
--   \le \bigl(6(N+1)\bigr)^{45}D_*.
--   $$
--
--   Here $N$ is the outer length. The common marginal factorials are retained exactly. Global entropy maximality of the target table controls the exponential part, and rowwise multinomial estimates contribute only the displayed polynomial factor.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, specialized using Section 5, Equation (5.2), printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the polynomial loss is a standard rowwise multinomial entropy refinement.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_completion_quotient_le_polynomial_target
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.fixedMarginalCount m j) :
    (((∏ j : Fin 9,
          (MME.StothersFourth.fixedMarginalCount m j).factorial) /
        ∏ sigma : MME.StothersFourth.FixedHashSupportTriple,
          (k sigma).factorial : ℕ) : ℝ) ≤
      (6 * (((MME.StothersFourth.fixedOuterLength m + 1 : ℕ) : ℝ))) ^ 45 *
        (MME.StothersFourth.fixedHashTargetStarDegree m : ℝ) := by
  sorry
