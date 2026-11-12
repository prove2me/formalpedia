-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_sl2_unique_involution
-- name    : OddOrder.Isaacs.Ch07.sl2_unique_involution
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:47:24.577603+00:00
-- url     : https://prove2.me/theorems/16e468de-2b93-4a54-a06d-f065131d8bfc
-- title:
--   Isaacs Lemma 7.4: the unique involution of $SL(2,F)$ in characteristic $\ne2$ is $-I$
-- statement:
--   Let $F$ be a field with $2\ne0$ in $F$ (characteristic not $2$), and let $t\in SL_2(F)$ satisfy $t^2=1$ and $t\ne1$. Then
--   $$t=-1\quad(\text{that is, } t=-I).$$
--
--   Equivalently, $-I$ is the unique involution of $SL_2(F)$. The case "$q$ odd" of Isaacs is the specialization $2\ne0$ in $F=\mathbb{Z}/q$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean#L100-L217

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

theorem sl2_unique_involution
    {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {t : Matrix.SpecialLinearGroup (Fin 2) F}
    (ht_sq : t ^ 2 = 1) (ht_ne : t ≠ 1) :
    t = -1 := by sorry

end OddOrder.Isaacs.Ch07
