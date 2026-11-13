-- Prove2me | Theorems.Thm_OddOrder_BG_Ch4_S14_exists_kappaHall_invariant_complement_to_MF
-- name    : OddOrder.BG.Ch4.S14.exists_kappaHall_invariant_complement_to_MF
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T10:23:34.654969+00:00
-- url     : https://prove2.me/theorems/4e9e675c-fcea-4025-9041-8fdbdc90aae8
-- title:
--   Peterfalvi (13.1.b): the derived subgroup of a type P maximal subgroup is $M_FU$ with $K\le N_G(U)$
-- statement:
--   Let $G$ be a finite group which is a minimal simple group of odd order (`IsMinimalSimpleOdd G`). Let $M$ be a maximal subgroup of $G$ of type P, let $K\le M$ be a cyclic subgroup that is a Hall $\kappa(M)$-subgroup of $M$ (that is, `K.subgroupOf M` is a Hall subgroup for the prime set $\kappa(M)$). Then there is a subgroup $U\le G$ such that
--   $$M'=M_F\sqcup U,\qquad K\le N_G(U),\qquad M_F\cap U=1,$$
--   where $M'$ is the derived subgroup of $M$ (taken inside $G$) and $M_F$ is the maximal nilpotent normal Hall subgroup of $M$.
--
--   This is part of Peterfalvi (13.1.b): the derived subgroup of a type P maximal subgroup is a semidirect product $M_F U$ with complement $U$ normalised by the cyclic $\kappa$-Hall subgroup $K$.
--
--   **Formalization Note** $M_F$ is `maxNilpotentNormalHall M`, $M'$ is `derivedInG M`, and $\sqcup$ is the join of subgroups; since $M_F$ is normal in $M$ and $M_F\cap U=1$, the join is a semidirect product.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePComplement.lean#L30-L90

import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Basics
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_SigmaLengthOne
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypePDuality
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_GlobalCounting
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
import Definitions.Def_OddOrder_GroupTheory_AInvariantComplement

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch4.S15

variable {G : Type*} [Group G] [Finite G]

theorem exists_kappaHall_invariant_complement_to_MF (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (kappa M) (K.subgroupOf M)) [IsCyclic ↥K] :
    ∃ U : Subgroup G, derivedInG M = maxNilpotentNormalHall M ⊔ U ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧ maxNilpotentNormalHall M ⊓ U = ⊥ := by sorry

end OddOrder.BG.Ch4.S14
