-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSideDelta_isReal
-- name    : OddOrder.Peterfalvi.S16.tSideDelta_isReal
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:33.332205+00:00
-- url     : https://prove2.me/theorems/91f2bd57-52f6-4baa-8764-203802c2620d
-- title:
--   Peterfalvi (14.9): the $T$-side residual $\Delta=\tau_T(\nu_0-\zeta)-1_G+\tau_1\zeta$ is real
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $T=$ `hyp.base.T` (with `Fintype G`, `Fintype ↥T` and invertibility of $|G|,|T|$ in $\mathbb{C}$). Write $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`, $\tau_T=$ `tSideDadeMap hyp hG`. Let $S$ be a set of class functions on $T$ and `coh : S07.IsCoherent τ_T S A₁(T)` with coherent extension $\tau_1=$ `coh.extension`. Let $\nu_0,\zeta$ be class functions on $T$ with $\zeta\in S$ and $\bar\zeta\in S$, such that
--
--   - $\nu_0-\zeta$ and $\zeta-\bar\zeta$ are supported in $A_1(T)$;
--   - $\overline{\nu_0-\zeta}=\nu_0-\bar\zeta$;
--   - $\overline{\tau_1\zeta}=\tau_1\bar\zeta$.
--
--   Then the class function
--   $$\Delta \;=\; \tau_T(\nu_0-\zeta)\;-\;1_G\;+\;\tau_1\zeta$$
--   on $G$ is real, i.e. `ClassFunction.IsReal Δ` (here $1_G$ is the trivial irreducible character viewed as a class function).
--
--   The Dade image commutes with conjugation, and coherence identifies $\tau_T(\zeta-\bar\zeta)$ with $\tau_1\zeta-\tau_1\bar\zeta$; these cancel in $\bar\Delta-\Delta$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean#L209-L273

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

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

open scoped Classical in

theorem tSideDelta_isReal [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ν0 ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S) (hζc : ζ.conj ∈ S)
    (hβsupp : (ν0 - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hdiffSupp : (ζ - ζ.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T)
    (hβconj : (ν0 - ζ).conj = ν0 - ζ.conj)
    (hExtConj : (coh.extension ζ).conj = coh.extension ζ.conj) :
    ClassFunction.IsReal
      (tSideDadeMap hyp hG (ν0 - ζ) -
        (trivialIrreducibleCharacter G : ClassFunction G ℂ) +
        coh.extension ζ) := by sorry

end OddOrder.Peterfalvi.S16
