-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_centralizes_commutator_of_card_prime_coprime
-- name    : OddOrder.Isaacs.Ch06.centralizes_commutator_of_card_prime_coprime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:45.817188+00:00
-- url     : https://prove2.me/theorems/7123e678-e5ed-4f15-901f-cb3963613e73
-- title:
--   In a Frobenius complement of odd order, a prime-order subgroup $R\nmid|A'|$ centralizes $A'$
-- statement:
--   Let $A$ be a finite group acting on a finite nontrivial group $U$ (`MulDistribMulAction A U`) with a Frobenius action (`IsFrobeniusAction A U`: every nonidentity element of $A$ fixes only the identity of $U$), such that $|A|$ is odd. Let $R\le A$ be a subgroup of prime order $r$ with $r\nmid|A'|$, where $A'$ is the commutator subgroup of $A$. Then
--   $$R\le C_A(A').$$
--
--   Step 2 of the proof that, in a Frobenius complement of odd order, subgroups of prime order are normal. $A$ is a Z-group (Step 1), so $A'$ is cyclic and normal. If $R$ did not centralize $A'$, then $[A',R]\ne1$ would contain a subgroup $S$ of prime order $s$, $R$-invariant with $C_S(R)=1$, and $R\sqcup S$ would be a noncyclic subgroup of order $rs$, contradicting Isaacs Thm 6.9.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean#L174-L296

import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

theorem centralizes_commutator_of_card_prime_coprime
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r)
    (hrN : ¬ r ∣ Nat.card ↥(commutator A)) :
    R ≤ Subgroup.centralizer ((commutator A : Subgroup A) : Set A) := by sorry

end OddOrder.Isaacs.Ch06
