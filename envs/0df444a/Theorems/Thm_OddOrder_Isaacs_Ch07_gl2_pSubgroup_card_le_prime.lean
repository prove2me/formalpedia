-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_gl2_pSubgroup_card_le_prime
-- name    : OddOrder.Isaacs.Ch07.gl2_pSubgroup_card_le_prime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:19.833459+00:00
-- url     : https://prove2.me/theorems/c48023e1-9d98-4d43-b41f-6f2cdd9d7498
-- title:
--   A $p$-subgroup of $GL_2(p)$ has order at most $p$
-- statement:
--   Let $p$ be a prime and $P\le GL_2(\mathbb{F}_p)$ a $p$-subgroup. Then
--   $$|P|\le p.$$
--
--   This is the cardinality step in Isaacs Thm 7.5, after embedding a faithful action on an elementary abelian group of order $p^2$ into $GL_2(p)$.
--
--   **Formalization Note** The ambient group is `Matrix.GeneralLinearGroup (Fin 2) (ZMod p)`; "$p$-subgroup" is `IsPGroup p P`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean#L308-L356

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

theorem gl2_pSubgroup_card_le_prime {p : ℕ} [Fact p.Prime]
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p))) (hP : IsPGroup p P) :
    Nat.card P ≤ p := by sorry

end OddOrder.Isaacs.Ch07
