-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_lem73_aux
-- name    : OddOrder.Isaacs.Ch07.lem73_aux
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:13.514322+00:00
-- url     : https://prove2.me/theorems/09080e57-0712-4b01-a77b-895008ea6eb1
-- title:
--   Isaacs Lemma 7.3 (induction form): a $p$-subgroup of $GL_2(p)$ normalizing $L$ centralizes it
-- statement:
--   Let $p$ be an odd prime ($p\ne2$) and let $P\le GL_2(\mathbb{F}_p)$ be a $p$-subgroup. Then for every $n\in\mathbb{N}$ and every subgroup $L\le GL_2(\mathbb{F}_p)$ such that
--
--   * $P\le N(L)$ (the normalizer of $L$),
--   * $p\nmid|L|$,
--   * every 2-subgroup $S\le L$ is abelian ($xy=yx$ for all $x,y\in S$),
--   * $|L|\le n$,
--
--   we have
--   $$P\le C(L).$$
--
--   This is the auxiliary form of Isaacs Lemma 7.3 for strong induction on $|L|$, with $p$ and $P$ fixed in advance and $L$ varying; the induction parameter is the bound $|L|\le n$.
--
--   **Formalization Note** The group is `Matrix.GeneralLinearGroup (Fin 2) (ZMod p)`; $p$-subgroups are `IsPGroup p P` and 2-subgroups `IsPGroup 2 S`. The statement quantifies over $n$ and $L$ inside the conclusion.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean#L740-L1252

import Definitions.Def_OddOrder_GroupTheory_OmegaSubgroup
import Definitions.Def_OddOrder_GroupTheory_ThompsonSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Main
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch07_ThompsonSubgroup_S7A1_JpGL2p
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination

namespace OddOrder.Isaacs.Ch07

open scoped commutatorElement

open scoped Pointwise

variable {G : Type*} [Group G]

theorem lem73_aux
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {P : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
    (hPp : IsPGroup p P) :
    ∀ (n : ℕ) {L : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))}
      (_hPnorm : P ≤ Subgroup.normalizer (L : Set _))
      (_hLcop : ¬ p ∣ Nat.card L)
      (_hL2abelian : ∀ S : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)),
        S ≤ L → IsPGroup 2 S → ∀ x y : ↥S, x * y = y * x),
      Nat.card L ≤ n →
      P ≤ Subgroup.centralizer (L : Set _) := by sorry

end OddOrder.Isaacs.Ch07
