-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_IsFrobeniusGroup_conjComplement
-- name    : OddOrder.Isaacs.Ch06.IsFrobeniusGroup.conjComplement
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:08.510312+00:00
-- url     : https://prove2.me/theorems/01aeed88-7613-4a2e-bc32-a80f1a873aa1
-- title:
--   A conjugate of a Frobenius complement is again a Frobenius complement
-- statement:
--   Let $G$ be a finite group and $N,A\le G$ subgroups such that $G$ is a Frobenius group with kernel $N$ and complement $A$ (`IsFrobeniusGroup G N A`: $N$ is a nontrivial normal subgroup, $A$ a nontrivial complement, and no nonidentity element of $A$ commutes with a nonidentity element of $N$). Then for every $g\in G$, $G$ is also a Frobenius group with kernel $N$ and complement the conjugate $gAg^{-1}$:
--   $$\texttt{IsFrobeniusGroup }G\ N\ (gAg^{-1}).$$
--
--   The normal kernel $N$ is fixed by conjugation. This is used to choose a complement containing a prescribed subgroup disjoint from the kernel.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean#L502-L553

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

theorem IsFrobeniusGroup.conjComplement {G : Type*} [Group G] [Finite G] {N A : Subgroup G}
    (h : IsFrobeniusGroup G N A) (g : G) :
    IsFrobeniusGroup G N (A.map (MulAut.conj g).toMonoidHom) := by sorry

end OddOrder.Isaacs.Ch06
