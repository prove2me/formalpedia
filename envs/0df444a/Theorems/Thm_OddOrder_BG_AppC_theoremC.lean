-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_theoremC
-- name    : OddOrder.BG.AppC.theoremC
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:34:23.762192+00:00
-- url     : https://prove2.me/theorems/17dc429a-410a-440b-987a-a50f8b55e345
-- title:
--   Bender--Glauberman Theorem C: the Section 16 field-normalizer configuration forces $p\le q$
-- statement:
--   Let $G$ be a finite group and let `hyp : S16.Hypothesis (G := G)` be a Peterfalvi Section 16 hypothesis, with associated primes $p=$ `hyp.base.p` and $q=$ `hyp.base.q`. If `S16.FieldNormalizerData hyp` holds (the field-normalizer configuration of Peterfalvi (14.2), packaged as a structure), then
--   $$p\le q.$$
--
--   This is Theorem C of Bender--Glauberman Appendix C, specialised to the Section 16 instance of Hypothesis (B). It is the final numerical input that, combined with the opposite inequality coming from the character theory, yields the contradiction in the Feit--Thompson proof.
--
--   **Formalization Note** The hypothesis `S16.FieldNormalizerData hyp` is a data-carrying structure (a `Type`), and the theorem is stated as an implication from it.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_FinalContradiction.lean#L159-L166

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

namespace OddOrder.BG.AppC

open OddOrder.GroupTheory

open OddOrder.Peterfalvi

open scoped Pointwise

variable {G : Type*} [Group G]

theorem theoremC [Finite G] (hyp : S16.Hypothesis (G := G)) :
    S16.FieldNormalizerData hyp → hyp.base.p ≤ hyp.base.q := by sorry

end OddOrder.BG.AppC
