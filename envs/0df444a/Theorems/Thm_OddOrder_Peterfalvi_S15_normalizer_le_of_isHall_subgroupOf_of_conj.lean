-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_normalizer_le_of_isHall_subgroupOf_of_conj
-- name    : OddOrder.Peterfalvi.S15.normalizer_le_of_isHall_subgroupOf_of_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:10:43.065481+00:00
-- url     : https://prove2.me/theorems/7b88f59c-008d-4342-8bbd-038998af86cf
-- title:
--   Structural core of Peterfalvi (13.17.a): $N_G(U)\le L$ and $L$ conjugate to $V$ imply $N_G(U)\le V$
-- statement:
--   Let $G$ be a finite group and $V,U,L\le G$ subgroups with $V$ solvable, $U\le V$, and $U$ a $\pi$-Hall subgroup of $V$ for some set of primes $\pi$ (`Ch03.IsHallSubgroup π (U.subgroupOf V)`). Suppose $gLg^{-1}=V$ for some $g\in G$ and $N_G(U)\le L$. Then
--
--   $$N_G(U)\le V .$$
--
--   This generic statement rules out the case $L\sim S$ in (8.8.b4) in the proof of (13.17.a) via conjugacy of Hall subgroups of solvable groups.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_SAndTBasic.lean#L1026-L1075

import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

theorem normalizer_le_of_isHall_subgroupOf_of_conj [Finite G] {V U L : Subgroup G}
    (hVsolv : Group.IsSolvable ↥V) (hUV : U ≤ V) {π : Set ℕ}
    (hUhall : Ch03.IsHallSubgroup π (U.subgroupOf V))
    {g : G} (hconj : MulAut.conj g • L = V)
    (hNUL : Subgroup.normalizer (U : Set G) ≤ L) :
    Subgroup.normalizer (U : Set G) ≤ V := by sorry

end OddOrder.Peterfalvi.S15
