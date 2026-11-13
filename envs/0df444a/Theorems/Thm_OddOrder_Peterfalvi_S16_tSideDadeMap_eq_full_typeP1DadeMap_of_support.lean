-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDadeMap_eq_full_typeP1DadeMap_of_support
-- name    : OddOrder.Peterfalvi.S16.tSideDadeMap_eq_full_typeP1DadeMap_of_support
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:07:35.450578+00:00
-- url     : https://prove2.me/theorems/36ec1cdd-6944-4199-841e-0de6a6497616
-- title:
--   Peterfalvi (2.11)/(13.2.e): $T$-side Dade map equals the full type-$P_1$ Dade map on $A_1(T)$-supported functions
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration (with `Fintype G`, `Fintype ↥T`, and $|G|$, $|T|$ invertible in $\mathbb{C}$), $T=$ `hyp.base.T`, `dataT : TypePData T` a type-$P$ datum, and assume $T$ is of type $P_1$ (`IsTypeP1 T`). Let $\varphi$ be a complex class function on $T$ whose support lies in $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`. Then
--   $$\tau_T(\varphi) \;=\; \tau^{\mathrm{full}}(\varphi),$$
--   where $\tau_T=$ `tSideDadeMap hyp hG` is the $T$-side Dade map used for the (14.9) coherent family, and $\tau^{\mathrm{full}}$ is the integral-character Dade map (`dadeIntegralCharacterMap`) of the full type-$P_1$ Dade support datum on $A_0(T)=A(T)\cup V^T$, obtained from `dadeSupportHypothesisData_typePA0_of_isTypeP1 hG hT_maximal dataT hP1`.
--
--   Thus $\tau_T$ is the restriction of the full type-$P_1$ Dade map to $A_1(T)$-supported class functions.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapCross.lean#L36-L97

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped BigOperators

open scoped Classical in

theorem tSideDadeMap_eq_full_typeP1DadeMap_of_support [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    [Fintype G] [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (dataT : OddOrder.GroupTheory.TypePData hyp.base.T)
    (hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 hyp.base.T)
    {φ : ClassFunction ↥hyp.base.T ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    tSideDadeMap hyp hG φ =
      let full := (OddOrder.Peterfalvi.S10.dadeSupportHypothesisData_typePA0_of_isTypeP1
        hG hyp.base.T_maximal dataT hP1).some
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap full.dade
        (full.dade.fullDadeIsometryData) φ := by sorry

end OddOrder.Peterfalvi.S16
