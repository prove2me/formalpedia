-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_exact_target_count_factorization
-- name    : MME.StothersFourth.mme_stothers_fixed_exact_target_count_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:19:17.09209+00:00
-- url     : https://prove2.me/theorems/fd54b5fc-1da1-40bd-a7dc-6a8c04df251a
-- title:
--   Marginal-times-completion factorization of the fixed Stothers target count
-- statement:
--   Let $N$ be the fixed outer length, let
--
--   $$
--   V=\frac{N!}{\prod_{j=0}^{8}M_j!}
--   $$
--
--   be the number of possible words in one mode with the prescribed marginal, and let $D_*$ be the fixed target completion degree. Then the exact target-address family has cardinality $V D_*$, and $D_*\ge1$. This is the target-count factorization required to normalize the affine-hash incidence argument.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Equations (3.3)--(3.4), printed pp. 354--356, and the fixed Section 5 type distribution, printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_exact_target_count_factorization
    (m : ℕ) :
    let N := MME.StothersFourth.fixedOuterLength m
    let V : ℝ :=
      (N.factorial : ℝ) /
        ∏ j : Fin 9,
          ((MME.StothersFourth.fixedMarginalCount m j).factorial : ℝ)
    (Nat.card
        {a : MME.StothersFourth.FixedMarginalSupportedAddress m //
          MME.StothersFourth.FixedHasExactJointProfile a} : ℝ) =
        V * (MME.StothersFourth.fixedHashTargetStarDegree m : ℝ) ∧
      1 ≤ MME.StothersFourth.fixedHashTargetStarDegree m := by
  sorry
