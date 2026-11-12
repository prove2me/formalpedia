-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch07_opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
-- name    : OddOrder.Isaacs.Ch07.opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:57.676435+00:00
-- url     : https://prove2.me/theorems/241e8735-e870-4f44-8665-0764c2960209
-- title:
--   If a non-normal Sylow $p$-subgroup has order at most $p$, then $O_p(G)=1$
-- statement:
--   Let $G$ be a finite group, $p$ a prime, and $P$ a Sylow $p$-subgroup of $G$ with $|P|\le p$ which is not normal in $G$. Then
--   $$O_p(G)=1,$$
--   where $O_p(G)$ is the largest normal $p$-subgroup (here the intersection of all Sylow $p$-subgroups).
--
--   This is the reduction $O_p(G)=1$ in Isaacs Thm 7.5, once the faithful action has embedded the group into $GL_2(p)$ and $|P|\le p$ has been established.
--
--   **Formalization Note** $O_p(G)$ is `Ch01.opCore p G`, defined as the infimum of all Sylow $p$-subgroups.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch07_ThompsonSubgroup/S7A1_JpGL2p.lean#L358-L396

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

theorem opCore_eq_bot_of_sylow_card_le_prime_of_not_normal
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP_card : Nat.card (P : Subgroup G) ≤ p)
    (hP_not_normal : ¬ (P : Subgroup G).Normal) :
    OddOrder.Isaacs.Ch01.opCore p G = ⊥ := by sorry

end OddOrder.Isaacs.Ch07
