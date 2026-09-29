-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_star_joint_table_fiber_le
-- name    : MME.StothersFourth.mme_stothers_fixed_star_joint_table_fiber_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T20:47:04.402889+00:00
-- url     : https://prove2.me/theorems/5aa05bb0-dd8d-4c36-9f19-5798507301b3
-- title:
--   Polynomial comparison for one fixed Stothers joint-table fiber
-- statement:
--   Fix a positive scale $m$, a finite family $E$ of marginal-supported Stothers outer addresses, an address $a$, and one mode. Let $k$ be a supported $45$-cell joint table that is realized inside the completion star of $a$. The number of star members realizing exactly $k$ is at most
--
--   $$
--   igl(6(N+1)igr)^{45}D_*,
--   $$
--
--   where $N$ is the outer length and $D_*$ is the completion degree of the fixed target joint table. The proof compares the nine row multinomials for $k$ with those of the target table. Entropy maximality controls the exponential term, while the explicit multinomial upper and lower estimates account only for the displayed polynomial factor.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, specialized using Section 5, Equation (5.2), printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the polynomial factor is obtained through standard rowwise multinomial entropy estimates.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_star_joint_table_fiber_le
    (m : ℕ) (hm : 0 < m)
    (E : Finset (MME.StothersFourth.FixedMarginalSupportedAddress m))
    (a : MME.StothersFourth.FixedMarginalSupportedAddress m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hk : k ∈ (E.filter (fun b ↦ b.1 i = a.1 i)).image
      MME.StothersFourth.fixedHashJointTable) :
    ((E.filter (fun b ↦ b.1 i = a.1 i)).filter
      (fun b ↦ MME.StothersFourth.fixedHashJointTable b = k)).card ≤
        (6 * (MME.StothersFourth.fixedOuterLength m + 1)) ^ 45 *
          MME.StothersFourth.fixedHashTargetStarDegree m := by
  sorry
