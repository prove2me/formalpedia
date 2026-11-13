-- Prove2me | Theorems.Thm_OddOrder_noMinimalSimpleOdd_of_section16
-- name    : OddOrder.noMinimalSimpleOdd_of_section16
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:43:30.36065+00:00
-- url     : https://prove2.me/theorems/a0aa747e-83dc-4088-8ccf-611334eccbcf
-- title:
--   No minimal simple group of odd order satisfies the Section 16 hypotheses (final contradiction)
-- statement:
--   Let $G$ be a finite group. Suppose $G$ is a minimal simple group of odd order (`IsMinimalSimpleOdd G`), no maximal subgroup of $G$ is of type V, the noncoherence refuter `H0CNoncoherenceRefuter G` holds, and `hyp : Peterfalvi.S16.Hypothesis (G := G)` is a Peterfalvi Section 16 hypothesis for $G$. Then
--   $$\text{False}.$$
--
--   This is the final contradiction bridge: from the minimal-counterexample hypotheses of Bender--Glauberman and the Peterfalvi Section 16 hypotheses, Appendix C of Bender--Glauberman (Theorem C) completes the contradiction.
--
--   **Formalization Note** `IsMinimalSimpleOdd G` bundles: $|G|$ odd, $G$ simple, $G$ not solvable, and every proper subgroup solvable. `IsTypeV`, `H0CNoncoherenceRefuter` and `S16.Hypothesis` are project definitions encoding the corresponding notions from Peterfalvi's text.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/FeitThompsonSection16Core.lean#L60-L68

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

theorem noMinimalSimpleOdd_of_section16 {G : Type*} [Group G] [Finite G]
    (hG : IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Peterfalvi.S16.Hypothesis (G := G)) :
    False := by sorry

end OddOrder
