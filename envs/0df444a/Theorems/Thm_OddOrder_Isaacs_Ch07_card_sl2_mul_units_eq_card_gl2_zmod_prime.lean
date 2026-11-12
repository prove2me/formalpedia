-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_card_sl2_mul_units_eq_card_gl2_zmod_prime
-- name    : OddOrder.Isaacs.Ch07.card_sl2_mul_units_eq_card_gl2_zmod_prime
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:53.728236+00:00
-- url     : https://prove2.me/theorems/53e4f42a-97e2-4bb0-9d36-ed98e4056bac
-- title:
--   Order identity $|SL_2(p)|\cdot(p-1)=|GL_2(p)|$
-- statement:
--   For every prime $p$,
--   $$|SL_2(\mathbb{Z}/p)|\cdot(p-1)=|GL_2(\mathbb{Z}/p)|.$$
--
--   That is, the order of the special linear group over $\mathbb{F}_p$ times $p-1$ equals the order of the general linear group (the determinant maps $GL_2(\mathbb{F}_p)$ onto $\mathbb{F}_p^{\times}$ with kernel $SL_2(\mathbb{F}_p)$).
--
--   **Formalization Note** The groups are `Matrix.SpecialLinearGroup (Fin 2) (ZMod p)` and `Matrix.GeneralLinearGroup (Fin 2) (ZMod p)`, with orders taken by `Nat.card`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean#L219-L290

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

theorem card_sl2_mul_units_eq_card_gl2_zmod_prime
    {p : ℕ} [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) * (p - 1) =
      Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) := by sorry

end OddOrder.Isaacs.Ch07
