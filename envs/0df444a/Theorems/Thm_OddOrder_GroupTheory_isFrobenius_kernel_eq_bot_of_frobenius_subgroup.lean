-- Prove2me | Theorems.Thm_OddOrder_GroupTheory_isFrobenius_kernel_eq_bot_of_frobenius_subgroup
-- name    : OddOrder.GroupTheory.isFrobenius_kernel_eq_bot_of_frobenius_subgroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:49:00.27255+00:00
-- url     : https://prove2.me/theorems/c7ef502d-b2e7-43e9-999d-b4d95a9a6fd9
-- title:
--   Peterfalvi (13.17.b): a Frobenius subgroup acting coprimely and disjointly forces the kernel to be trivial
-- statement:
--   Let $G$ be a finite group and $N,U,E,L\le G$ subgroups with $N\le L$ and $U\sqcup E\le L$ (the join $UE$). Assume:
--
--   * $L$ is a Frobenius group with kernel $N$ (for some complement $A\le L$, `IsFrobeniusGroup L N A`);
--   * $U\sqcup E$ is a Frobenius group with kernel $U$ and complement $E$;
--   * $U\cap N=1$ and $E\cap N=1$;
--   * $N$ is solvable;
--   * $\gcd(|N|,|U\sqcup E|)=1$.
--
--   Then $N=1$.
--
--   Both $U$ and $E$ act fixed-point-freely on $N$ (each nontrivial element lies outside the Frobenius kernel, so its centralizer meets $N$ trivially), hence Wielandt's formula for a coprime Frobenius action forces $|N|=1$. This is the engine of Peterfalvi (13.17.b), where it gives $|L_F|=1$ from $U\cap L_F=1$.
--
--   **Formalization Note** `Ch06.IsFrobeniusGroup G N A` is a structure asserting that $N$ is a nontrivial normal subgroup, $A$ is a nontrivial complement, and no nonidentity element of $A$ commutes with a nonidentity element of $N$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/WielandtFixedPoint.lean#L171-L240

import Definitions.Def_OddOrder_GroupTheory_CoprimeAction
import Definitions.Def_OddOrder_GroupTheory_WielandtPerFactorDischarge
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_WielandtElabFrobenius
import Definitions.Def_OddOrder_GroupTheory_WielandtFixedPoint

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.Isaacs.Ch03 (IsAInvariant)

section FrobeniusCentralizer

theorem isFrobenius_kernel_eq_bot_of_frobenius_subgroup {G : Type*} [Group G] [Finite G]
    {Lsub N U E : Subgroup G} (hNL : N ≤ Lsub) (hUL : U ⊔ E ≤ Lsub)
    (hFrob : ∃ A : Subgroup ↥Lsub, Ch06.IsFrobeniusGroup ↥Lsub (N.subgroupOf Lsub) A)
    (hUE : Ch06.IsFrobeniusGroup ↥(U ⊔ E) (U.subgroupOf (U ⊔ E)) (E.subgroupOf (U ⊔ E)))
    (hUN : U ⊓ N = ⊥) (hEN : E ⊓ N = ⊥) (hsolv : Group.IsSolvable ↥N)
    (hcop : Nat.Coprime (Nat.card ↥N) (Nat.card ↥(U ⊔ E))) :
    N = ⊥ := by sorry

end FrobeniusCentralizer

end OddOrder.GroupTheory
