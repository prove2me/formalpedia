-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_exists_LHypothesis
-- name    : OddOrder.Peterfalvi.S16.exists_LHypothesis
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:18:15.932809+00:00
-- url     : https://prove2.me/theorems/e60ee392-38bf-4c64-9ca4-b797e498614f
-- title:
--   Peterfalvi (14.3): a type-I maximal subgroup $L$ over $N_G(U)$ exists
-- statement:
--   Let $G$ be a finite minimal simple odd-order group with no maximal subgroup of type V (`hnoV`), assume `hncH0C : S13.H0CNoncoherenceRefuter G`, and let `hyp` be a Peterfalvi §14 configuration for $G$. Then the type `LHypothesis hyp` is nonempty:
--   $$\texttt{Nonempty}\ (\texttt{LHypothesis hyp}).$$
--
--   That is, there is a type-I maximal subgroup $L$ of $G$ over $N_G(U)$ together with the structural data (type-I-over-normalizer Frobenius structure, with complement of order $pq$) that the §14 non-existence argument consumes.
--
--   **Formalization Note.** `LHypothesis hyp` is a bundled structure of the project; the Dade (14.3.b) data is deliberately not part of it.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean#L38-L73

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
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas
import Definitions.Def_OddOrder_Peterfalvi_S07_CoherenceGalois
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_GaloisInnerTransport
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_TGapGridAlignment
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndTDefs
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem exists_LHypothesis [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hnoV : ¬ ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ OddOrder.GroupTheory.IsTypeV M)
    (hncH0C : OddOrder.Peterfalvi.S13.H0CNoncoherenceRefuter G)
    (hyp : Hypothesis (G := G)) :
    Nonempty (LHypothesis hyp) := by sorry

end OddOrder.Peterfalvi.S16
