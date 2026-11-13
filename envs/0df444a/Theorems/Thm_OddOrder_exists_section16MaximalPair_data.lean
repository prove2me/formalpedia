-- Prove2me | Theorems.Thm_OddOrder_exists_section16MaximalPair_data
-- name    : OddOrder.exists_section16MaximalPair_data
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:43:42.51933+00:00
-- url     : https://prove2.me/theorems/2a206b37-6da7-4063-9505-150bb320bc66
-- title:
--   Canonical type P maximal pair with $\kappa$-Hall data in a minimal simple group of odd order
-- statement:
--   Let $G$ be a finite group which is a minimal simple group of odd order (`IsMinimalSimpleOdd G`) having no maximal subgroup of type V. Then there exist subgroups $S,T,K,K^*\le G$ such that:
--
--   * $S,T$ are maximal subgroups of $G$, $S\ne T$, both are not of type I, and at least one of them is of type II;
--   * every maximal subgroup $M$ of $G$ is of type I or is conjugate to $S$ or to $T$;
--   * $K\le S$ is a Hall $\kappa(S)$-subgroup of $S$, and $K^*=M_\sigma(S)\cap C_G(K)$;
--   * $S$ and $T$ are of type P and are not conjugate in $G$;
--   * $K^*\le T$ is a Hall $\kappa(T)$-subgroup of $T$, and $K=M_\sigma(T)\cap C_G(K^*)$;
--   * $K\sqcup K^*$ is cyclic, and $|K|<|K^*|$.
--
--   This is the canonical type P dual pair $S,T$ together with the full $\kappa$-Hall witness data of Bender--Glauberman Theorem 14.7 (type P duality). Case (a) of (8.8) (every maximal subgroup of type I) is excluded by Peterfalvi (12.17). The data makes the intersection $S\cap T=K\times K^*$ available for building the type P structure.
--
--   **Formalization Note** `kappa`, `Msigma`, `IsTypeI`, `IsTypeII`, `IsTypeNonI`, `IsTypeP`, `IsTypeV` and `Ch03.IsHallSubgroup` are project definitions encoding the Bender--Glauberman notions; conjugacy of maximal subgroups is expressed through `MulAut.conj g • M`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonSection16Core.lean#L574-L666

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_BG_AppC_FrobeniusClassSum
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TSideTypeP
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisBasics
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_HypothesisSwap
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_PairStructure
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_Canonicalization
import Definitions.Def_OddOrder_Peterfalvi_S13_ElementaryAbelianKernel
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S07_Theorem74
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedIrreducible
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ColumnOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
import Definitions.Def_OddOrder_Peterfalvi_S16_GridExpansion
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEngines
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeSupply
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_CoherentProjectionRigidity
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
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
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCharacters
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S13_Section16PairData
import Definitions.Def_OddOrder_FeitThompsonSection16Core

namespace OddOrder

open OddOrder.BG

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.RepresentationTheory

open scoped Pointwise

universe u

section

open scoped OddOrder.Peterfalvi.S15.FiniteInduce

theorem exists_section16MaximalPair_data {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M) :
    ∃ S T K Kstar : Subgroup G,
      S ∈ maximalSubgroups G ∧ T ∈ maximalSubgroups G ∧ S ≠ T ∧
      IsTypeNonI S ∧ IsTypeNonI T ∧ (IsTypeII S ∨ IsTypeII T) ∧
      (∀ M : Subgroup G, M ∈ maximalSubgroups G →
        IsTypeI M ∨ (∃ g : G, MulAut.conj g • M = S) ∨ (∃ g : G, MulAut.conj g • M = T)) ∧
      K ≤ S ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa S) (K.subgroupOf S) ∧
      Kstar = BG.Ch3.S10.Msigma S ⊓ Subgroup.centralizer (K : Set G) ∧
      BG.Ch4.S14.IsTypeP S ∧ BG.Ch4.S14.IsTypeP T ∧ ¬ BG.Ch4.S14.IsConjugateSubgroup S T ∧
      Kstar ≤ T ∧ Ch03.IsHallSubgroup (BG.Ch4.S14.kappa T) (Kstar.subgroupOf T) ∧
      K = BG.Ch3.S10.Msigma T ⊓ Subgroup.centralizer (Kstar : Set G) ∧
      IsCyclic ↥(K ⊔ Kstar) ∧ Nat.card ↥K < Nat.card ↥Kstar := by sorry

end

end OddOrder
