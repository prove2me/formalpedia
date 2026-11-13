-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_calT1_difference_support
-- name    : OddOrder.Peterfalvi.S16.T_typeIII_calT1_difference_support
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:05:19.417359+00:00
-- url     : https://prove2.me/theorems/f2542197-d1a9-4591-a01e-5747af7f4dbb
-- title:
--   Peterfalvi (14.9): differences of members of the type-III family are supported on $A_1(T)=(T')^\#$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $T=$ `hyp.base.T`, assume $T$ is of type III, and $T'=$ `(derivedInG T).subgroupOf T` with the usual finiteness and invertibility instances. Let $\mathcal{T}$ be a finite set of irreducible characters of $T'$ all of which are linear ($\theta(1)=1$), and let $S$ be the set of class functions $\{\mathrm{Ind}_{T'}^{T}\theta:\theta\in\mathcal{T}\}$ on $T$. Then for all $a,b\in S$,
--   $$\operatorname{supp}(a-b)\;\subseteq\;A_1(T)=\texttt{supportInSubgroup (sigmaSharp T) T}.$$
--
--   Normality of $T'$ makes each induced character vanish off $T'$, and the common linear source degree makes a difference of members vanish at $1$. This is the source-support input shared by the coherence construction and the (5.3.b) $\eta$-orthogonality argument.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean#L472-L529

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped Classical in

theorem T_typeIII_calT1_difference_support [Finite G] (hyp : Hypothesis (G := G))
    [Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hlinear : ∀ θ ∈ 𝒯, (θ.toClassFunction :
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) → ℂ) 1 = 1)
    (calT1_set : Set (ClassFunction ↥hyp.base.T ℂ))
    (hcalT1 : calT1_set = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction))) :
    ∀ a ∈ calT1_set, ∀ b ∈ calT1_set,
      (a - b).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T := by sorry

end OddOrder.Peterfalvi.S16
