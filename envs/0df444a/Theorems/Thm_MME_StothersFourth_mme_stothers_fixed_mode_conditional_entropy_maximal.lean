-- Prove2me | Theorems.Thm_MME_StothersFourth_mme_stothers_fixed_mode_conditional_entropy_maximal
-- name    : MME.StothersFourth.mme_stothers_fixed_mode_conditional_entropy_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:09:05.120669+00:00
-- url     : https://prove2.me/theorems/52f97f3e-faf1-429b-8e03-3ab8716f7b69
-- title:
--   Conditional entropy maximality in every fixed Stothers mode
-- statement:
--   Let $k$ be any supported joint table with the fixed Stothers marginal, and fix one mode $i$. Weight the entropy of each conditional row by its marginal count. The fixed target table maximizes their total:
--
--   $$
--   \sum_{j=0}^{8}M_j H_2\!\left((k_\sigma/M_j)_{\sigma_i=j}\right)
--   \le
--   \sum_{j=0}^{8}M_j H_2\!\left((k^*_\sigma/M_j)_{\sigma_i=j}\right).
--   $$
--
--   This is the chain-rule form of global $45$-cell entropy maximality. It preserves the fixed marginal entropy exactly and is the exponential comparison required for completion-star degrees.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Lemma 3.3 and Equation (3.4), printed pp. 354--356, specialized to the maximum-entropy fixed joint distribution in Section 5, printed pp. 367--368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; the displayed implication is Shannon's entropy chain rule.

import Definitions.Def_mme_stothers_fixed_outer_profile
import Definitions.Def_mme_stothers_fixed_joint_tables
import Definitions.Def_mme_modern_entropy_data

open MME BigOperators

set_option autoImplicit false

theorem MME.StothersFourth.mme_stothers_fixed_mode_conditional_entropy_maximal
    (m : ℕ) (hm : 0 < m) (i : Fin 3)
    (k : MME.StothersFourth.FixedHashJointMultiplicityTable)
    (hkMarginal : ∀ l : Fin 3, ∀ j : Fin 9,
      (∑ sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 l = j},
        k sigma.1) = MME.StothersFourth.fixedMarginalCount m j) :
    (∑ j : Fin 9, (MME.StothersFourth.fixedMarginalCount m j : ℝ) *
      mme_modern_entropyBits
        (fun sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 i = j} ↦
          (k sigma.1 : ℝ) /
            (MME.StothersFourth.fixedMarginalCount m j : ℝ))) ≤
      ∑ j : Fin 9, (MME.StothersFourth.fixedMarginalCount m j : ℝ) *
        mme_modern_entropyBits
          (fun sigma : {sigma : MME.StothersFourth.FixedHashSupportTriple // sigma.1 i = j} ↦
            (MME.StothersFourth.fixedHashTargetJointTable m sigma.1 : ℝ) /
              (MME.StothersFourth.fixedMarginalCount m j : ℝ)) := by
  sorry
