-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_T_typeIII_coherent_image_inner_eta_eq_zero
-- name    : OddOrder.Peterfalvi.S16.T_typeIII_coherent_image_inner_eta_eq_zero
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:05:24.521658+00:00
-- url     : https://prove2.me/theorems/efc53831-d294-4918-8260-e8208d2862af
-- title:
--   Peterfalvi (5.3.b): $T$-side coherent images are orthogonal to the shared $\eta$-grid
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $T=$ `hyp.base.T` of type III (with `Fintype G`, `Fintype T`, $|G|,|T|$ invertible in $\mathbb{C}$). Let $S$ be a set of class functions on $T$ which is closed under conjugation (`ClosedUnderConjugate S`), has no real characters (`HasNoRealCharacters S`), and satisfies $\operatorname{supp}(\zeta-\bar\zeta)\subseteq A_1(T)=$ `supportInSubgroup (sigmaSharp T) T` for all $\zeta\in S$. Let `coh : S07.IsCoherent (tSideDadeMap hyp hG) S A₁(T)` be a coherence datum and $\zeta\in S$ an irreducible character. Then for all $i<q$ and $j<p$,
--   $$\langle\, \texttt{coh.extension}\ \zeta,\ \eta_{ij}\,\rangle \;=\;0 .$$
--
--   The coherent conjugate difference agrees with the Dade map on $A_1(T)$, which is the restriction of the full type-$P_1$ Dade map; vanishing on the regular set and conjugacy invariance then allow the (3.7)--(3.8) norm-two argument to give the orthogonality.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TTypeIICoherence.lean#L531-L657

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

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in

theorem T_typeIII_coherent_image_inner_eta_eq_zero [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    [fintypeG : Fintype G] [invertibleG : Invertible (Nat.card G : ℂ)]
    [Fintype ↥hyp.base.T] [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hconj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S)
    (hnoReal : OddOrder.Peterfalvi.S03.HasNoRealCharacters S)
    (hsupp : ∀ ζ ∈ S, (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ) :
    ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
      ClassFunction.inner (coh.extension ζ) (hyp.base.eta i j) = 0 := by sorry

end OddOrder.Peterfalvi.S16
