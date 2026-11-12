-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch05_OPrime_index_isPGroup
-- name    : OddOrder.Isaacs.Ch05.OPrime_index_isPGroup
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:29:12.439209+00:00
-- url     : https://prove2.me/theorems/f16e7c72-6d3a-4a97-b09b-e80ed3cb5195
-- title:
--   The subgroup $O^p(G)$ has $p$-power index
-- statement:
--   Let $G$ be a finite group and $p$ a prime. Let $O^p(G)$ denote the intersection of all normal subgroups of $G$ whose index is a power of $p$. Then there is $k\in\mathbb{N}$ with
--   $$[G:O^p(G)]=p^k.$$
--
--   The proof embeds $G/O^p(G)$ into the product of the quotients $G/N$ over the finitely many normal subgroups $N$ of $p$-power index, and applies Lagrange's theorem.
--
--   **Formalization Note** $O^p(G)$ is `OPrime p G`, defined as an infimum over the subtype of normal subgroups of $p$-power index.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch05_Transfer/Basic.lean#L944-L1005

import Definitions.Def_OddOrder_GroupTheory_CyclicSubgroupUniqueness
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_Isaacs_Ch05_Transfer_Basic
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Focal
import Mathlib.GroupTheory.Schreier
import Mathlib.GroupTheory.SpecificGroups.ZGroup

open scoped commutatorElement

open scoped IsMulCommutative

namespace OddOrder.Isaacs.Ch05

open Pointwise

open scoped commutatorElement

variable {G : Type*} [Group G]

section

theorem OPrime_index_isPGroup (p : ℕ) (G : Type*) [Group G] [Finite G] [Fact p.Prime] :
    ∃ k : ℕ, (OPrime p G).index = p ^ k := by sorry

end

end OddOrder.Isaacs.Ch05
