-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSideCoherentExtension_inner_trivial
-- name    : OddOrder.Peterfalvi.S16.tSideCoherentExtension_inner_trivial
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:32:42.302206+00:00
-- url     : https://prove2.me/theorems/46d96dbe-14fa-4706-9984-034252140aff
-- title:
--   Peterfalvi (7.8.a), $T$-side: the coherent extension $\tau_1\zeta$ is orthogonal to $1_G$
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration, $T=$ `hyp.base.T`, with `Fintype G`, `Fintype ↥T` and $|G|$, $|T|$ invertible in $\mathbb{C}$. Write $A_1(T)=T_\sigma^\#$ for `supportInSubgroup (sigmaSharp T) T`, and $\tau_T=$ `tSideDadeMap hyp hG`. Let $S$ be a set of class functions on $T$ with `hyp07 : S07.Hypothesis S A₁(T)` (the Peterfalvi §7 hypothesis for $T$) and `coh : S07.IsCoherent τ_T S A₁(T)` a coherence datum, with coherent extension `coh.extension`. Let $\zeta\in S$ be an irreducible character of $T$ with $\langle\zeta,1_T\rangle=0$ and with $\bar\zeta-\zeta$ supported in $A_1(T)$. Then
--   $$\langle\, \texttt{coh.extension}\ \zeta,\ 1_G\,\rangle \;=\; 0 .$$
--
--   The proof combines the $T$-side (2.7) adjoint identity with the generic equal-degree coherent-pair argument of (7.8.a).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean#L19-L91

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

theorem tSideCoherentExtension_inner_trivial [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {S : Set (ClassFunction ↥hyp.base.T ℂ)}
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    {ζ : ClassFunction ↥hyp.base.T ℂ}
    (hζ : ζ ∈ S)
    (hζirr : IsIrreducibleCharacter ζ)
    (hζ1 : ClassFunction.inner ζ (trivialClassFunction ↥hyp.base.T) = 0)
    (hsupp : (ζ.conj - ζ).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T) :
    ClassFunction.inner (coh.extension ζ) (trivialClassFunction G) = 0 := by sorry

end OddOrder.Peterfalvi.S16
