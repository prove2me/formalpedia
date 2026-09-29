-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_full_marginal_star_degree_le
-- name    : MME.StothersFourth.mme_stothers_fixed_full_marginal_star_degree_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:44:03.670567+00:00
-- url     : https://prove2.me/theorems/a720ea28-eb7b-418e-a364-8de1520b256c
-- title:
--   Polynomial completion-star bound for the fixed Stothers profile
-- statement:
--   Fix a positive scale $m$ in the exact Davie--Stothers fourth-power profile, let $N$ be the outer address length, and let $E$ be any finite family of supported addresses having the prescribed nine-grade marginal in every mode. For an address $a$ and a chosen mode, consider the completion star consisting of the members of $E$ whose word in that mode agrees with $a$. If $D_*$ is the exact number of completions having the fixed target 45-cell joint table, then
--
--   $$
--   |\operatorname{Star}_i(a;E)|\le (N+1)^{45}\bigl(6(N+1)\bigr)^{45}D_*.
--   $$
--
--   The first polynomial factor counts possible 45-cell joint tables. The second comes from applying upper and lower multinomial entropy bounds row by row across the nine grades, using the fixed joint distribution's global maximum-entropy property. In particular, the estimate retains the common marginal multinomial and incurs no exponential loss. This is the maximum-degree input for the Salem--Spencer collision pruning in Lemma 3.3.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, specialized using Section 5, Equation (5.2), printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the polynomial type-class estimate is the standard method-of-types refinement of the same proof.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_full_marginal_star_degree_le
    (m : ℕ) (hm : 0 < m)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3) :
    (E.filter (fun b ↦ b.1 i = a.1 i)).card ≤
      (MME.StothersFourth.fixedOuterLength m + 1) ^ 45 *
        ((6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m) := by
  sorry
