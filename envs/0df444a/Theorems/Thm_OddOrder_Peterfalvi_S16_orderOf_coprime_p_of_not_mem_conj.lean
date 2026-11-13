-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_orderOf_coprime_p_of_not_mem_conj
-- name    : OddOrder.Peterfalvi.S16.orderOf_coprime_p_of_not_mem_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:29:59.306829+00:00
-- url     : https://prove2.me/theorems/6ad4b8e6-d38c-4dd9-8aa3-16afe8b01419
-- title:
--   Peterfalvi (14.11.3), $S$-side: elements outside the conjugates of $W^\#$ and $P^\#$ have order prime to $p$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group and `hyp` a Peterfalvi §13 configuration for $G$ with prime $p$ and subgroups $S, P, W$. Assume the Frobenius-kernel property
--   $$\forall x\in P^\#,\quad S' \cap C_G(x) \le P ,$$
--   where $P^\#$ is `sharpSubgroup hyp.P` (the nonidentity elements of $P$) and $S'$ is the derived subgroup of $S$ taken in $G$ (`derivedInG hyp.S`). Let $g\in G$ lie in neither the set of $G$-conjugates of $W^\#$ nor the set of $G$-conjugates of $P^\#$ (`conjClassSet`). Then
--   $$\gcd\bigl(|g|,\,p\bigr)=1,$$
--   i.e. the order of $g$ is prime to $p$.
--
--   This is the $S$-side core of (14.11.3): the contrapositive shows that if $p$ divides $|g|$ then $g$ is conjugate into $P^\#$ or $W^\#$, using the decomposition $S = S' \rtimes W_1$ and the coprime coset collapse (2.1).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_G0Coprime.lean#L412-L533

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

theorem orderOf_coprime_p_of_not_mem_conj [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : OddOrder.Peterfalvi.S15.Hypothesis (G := G))
    (hfrob : ∀ x ∈ sharpSubgroup hyp.P,
      derivedInG hyp.S ⊓ Subgroup.centralizer ({x} : Set G) ≤ hyp.P) {g : G}
    (hW : g ∉ conjClassSet (sharpSubgroup hyp.W))
    (hP : g ∉ conjClassSet (sharpSubgroup hyp.P)) :
    Nat.Coprime (orderOf g) hyp.p := by sorry

end OddOrder.Peterfalvi.S16
