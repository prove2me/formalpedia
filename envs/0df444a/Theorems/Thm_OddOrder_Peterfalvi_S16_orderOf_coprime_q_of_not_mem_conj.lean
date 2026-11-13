-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_orderOf_coprime_q_of_not_mem_conj
-- name    : OddOrder.Peterfalvi.S16.orderOf_coprime_q_of_not_mem_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:32:55.275858+00:00
-- url     : https://prove2.me/theorems/68ae82cc-7413-4475-b64d-37068496f557
-- title:
--   Peterfalvi (14.11.3), $T$-side: elements outside the conjugates of $W^\#$ and $Q^\#$ have order prime to $q$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group and `hyp` a Peterfalvi §13 configuration for $G$ with prime $q$ and subgroups $T, Q, W$. Assume $T$ is of type II (`IsTypeII hyp.T`) and the Frobenius-kernel property
--   $$\forall x\in Q^\#,\quad T'\cap C_G(x) \le Q,$$
--   where $Q^\#$ is `sharpSubgroup hyp.Q` and $T'$ is the derived subgroup of $T$ in $G$. Let $g\in G$ lie in neither the set of $G$-conjugates of $W^\#$ nor that of $Q^\#$. Then
--   $$\gcd\bigl(|g|,\,q\bigr)=1 .$$
--
--   This is the dual of the $S$-side statement, along $T = T'\rtimes W_2$ with $T' = Q\rtimes V$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_G0Coprime.lean#L639-L753

import Definitions.Def_OddOrder_Peterfalvi_S15_BridgeCharacter
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S15_SSideGaloisFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTGrid
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_G0Coprime

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open scoped Pointwise

variable {G : Type*} [Group G]

theorem orderOf_coprime_q_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G)) (hTII : IsTypeII hyp.T)
    (hfrobT : ∀ x ∈ sharpSubgroup hyp.Q,
      derivedInG hyp.T ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.Q) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hQ : g ∉ conjClassSet (sharpSubgroup hyp.Q)) :
    Nat.Coprime (orderOf g) hyp.q := by sorry

end OddOrder.Peterfalvi.S16
