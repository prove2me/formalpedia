-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_exists_yD_mem_actionCommutator_conj_s_eq_t
-- name    : OddOrder.BG.AppC.FieldNormalizerData.exists_yD_mem_actionCommutator_conj_s_eq_t
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:21:52.57038+00:00
-- url     : https://prove2.me/theorems/6f0871e8-84b8-465f-8da8-5c356cd00f84
-- title:
--   BG Appendix C, Remark (XI): the conjugator can be taken in $[Q,W_2]$
-- statement:
--   Let `data : FieldNormalizerData p q G` be the field-normalizer data of Bender--Glauberman Appendix C. Write $s=\sigma(1_{P_0})\in W_2=\sigma(P_0)$, let $y\in Q$ be the distinguished element and $t=ysy^{-1}$. Here $W_2$ acts on the abelian $p'$-group $Q$ by conjugation (the homomorphism `data.w2ConjQAut : W₂ →* MulAut Q`). Then there is $y_D\in Q$ lying in the action commutator $[Q,W_2]$ of this action such that
--   $$ y_D\,s\,y_D^{-1}=t.$$
--
--   This is Remark (XI) of Appendix C: writing $Q=[Q,W_2]\,C_Q(W_2)$, the centralizer component of $y$ commutes with $s$, so we may assume $y\in[Q,W_2]$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean#L1034-L1073

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

theorem exists_yD_mem_actionCommutator_conj_s_eq_t
    (data : FieldNormalizerData p q G) :
    ∃ yD : ↥data.Q,
      yD ∈ OddOrder.Isaacs.Ch04.actionCommutator data.w2ConjQAut ∧
        MulAut.conj (yD : G) data.s = data.t := by sorry

end FieldNormalizerData

end OddOrder.BG.AppC
