-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_inner_trivial
-- name    : OddOrder.Peterfalvi.S16.tSideDadeMap_inner_trivial
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:36:54.929042+00:00
-- url     : https://prove2.me/theorems/4dbfcb1f-035c-4ea4-bdd5-0bb25f977265
-- title:
--   Peterfalvi (2.7), $T$-side: $\tau_T$ preserves the multiplicity of the trivial character on $A_1(T)$-supported functions
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration, $T=$ `hyp.base.T` (with `Fintype G`, `Fintype ↥T` and $|G|,|T|$ invertible in $\mathbb{C}$). Let $\varphi$ be a complex class function on $T$ whose support lies in $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`. Then, with $\tau_T=$ `tSideDadeMap hyp hG`,
--   $$\langle\tau_T(\varphi),\,1_G\rangle \;=\; \langle \varphi,\,1_T\rangle .$$
--
--   That is, a class function supported on $A_1(T)=T_\sigma^\#$ has the same trivial-character multiplicity before and after applying $\tau_T$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapPrimeTI.lean#L346-L391

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

open scoped Classical in

theorem tSideDadeMap_inner_trivial [Finite G]
    (hyp : Hypothesis (G := G)) [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφ : φ.support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (tSideDadeMap hyp hG φ) (trivialClassFunction G) =
      ClassFunction.inner φ (trivialClassFunction ↥hyp.base.T) := by sorry

end OddOrder.Peterfalvi.S16
