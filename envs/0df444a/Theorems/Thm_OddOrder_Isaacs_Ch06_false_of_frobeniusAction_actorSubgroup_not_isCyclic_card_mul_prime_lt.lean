-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
-- name    : OddOrder.Isaacs.Ch06.false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:35:04.638218+00:00
-- url     : https://prove2.me/theorems/3b80d163-52a1-4ad4-b233-d6f3bba49ee1
-- title:
--   Isaacs Theorem 6.9 ($p>q$ case): a Frobenius actor has no noncyclic subgroup of order $pq$ with $q<p$
-- statement:
--   Let $A$ be a group acting by automorphisms on a finite nontrivial group $U$ (`MulDistribMulAction A U`) such that the action is Frobenius (`IsFrobeniusAction A U`: every nonidentity $a\in A$ fixes only the identity of $U$). Let $B\le A$ be a finite subgroup of order $|B|=pq$ with $p,q$ primes and $q<p$. Then $B$ is cyclic; equivalently, the assumption that $B$ is not cyclic leads to a contradiction: $\text{False}$.
--
--   Such a subgroup $B$ would be a solvable Frobenius group: its Sylow $p$-subgroup is normal, a Sylow $q$-subgroup is a complement, and any fixed nonidentity pair would generate the whole group cyclically. This is the $p>q$ branch of Isaacs Thm 6.9 for subgroups of order $pq$.
--
--   **Formalization Note** The statement is given as `¬ IsCyclic B → False`; $A$ is not assumed finite.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/FrobeniusGroup.lean#L1106-L1199

import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusActionTI
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

section

theorem false_of_frobeniusAction_actorSubgroup_not_isCyclic_card_mul_prime_lt
    {A U : Type*} [Group A] [Group U] [Finite U] [Nontrivial U]
    [MulDistribMulAction A U]
    (hFrob : IsFrobeniusAction A U) (B : Subgroup A) [Finite B]
    {p q : ℕ} [hp : Fact p.Prime] [hq : Fact q.Prime]
    (hqp : q < p) (hCard : Nat.card B = p * q)
    (hNotCyclic : ¬ IsCyclic B) :
    False := by sorry

end

end OddOrder.Isaacs.Ch06
