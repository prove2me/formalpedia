-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_tSideCoherentExtension_conj
-- name    : OddOrder.Peterfalvi.S16.tSideCoherentExtension_conj
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:34:26.68729+00:00
-- url     : https://prove2.me/theorems/d3c73b3b-9855-4ff5-9408-3132b32ac793
-- title:
--   Peterfalvi (5.9.a), type-III $T$-side: the coherent extension commutes with complex conjugation
-- statement:
--   Let $G$ be a finite minimal simple odd-order group, `hyp` a Peterfalvi §14 configuration with $T=$ `hyp.base.T`, and assume $T$ is of type III (`IsTypeIII T`). Let $T' = T'$ denote the derived subgroup of $T$ (`(derivedInG T).subgroupOf T`), regarded as a subgroup of $T$; we are given the usual finiteness/invertibility instances for $G$, $T$, $T'$. Let $\mathcal{T}$ be a finite set of irreducible characters of $T'$, all nontrivial, and let $S$ be the set of class functions on $T$ given by
--   $$S=\{\mathrm{Ind}_{T'}^{T}\theta:\ \theta\in\mathcal{T}\}.$$
--   Let `hyp07 : S07.Hypothesis S A₁(T)` where $A_1(T)=$ `supportInSubgroup (sigmaSharp T) T`, let `coh : S07.IsCoherent (tSideDadeMap hyp hG) S A₁(T)` be a coherence datum, assume every $\chi\in S$ is an irreducible character of $T$, and let $\zeta\in S$. Then
--   $$\overline{\texttt{coh.extension}\ \zeta} \;=\; \texttt{coh.extension}\ \bar\zeta .$$
--
--   The extension of the family of degree-$p$ characters induced from $T'$ commutes with complex conjugation; the needed support condition follows because every element of the integral span vanishing at $1$ is supported on $(T')^\#=A_1(T)$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/TGapDelta.lean#L127-L207

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

theorem tSideCoherentExtension_conj [Finite G]
    (hyp : Hypothesis (G := G))
    [Fintype G] [Fintype ↥hyp.base.T]
    [Finite ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T)]
    [Invertible (Nat.card G : ℂ)]
    [Invertible (Nat.card ↥hyp.base.T : ℂ)]
    [Invertible
      (Nat.card ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hIII : OddOrder.GroupTheory.IsTypeIII hyp.base.T)
    (𝒯 : Finset (IrreducibleCharacter
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T)))
    (hne : ∀ θ ∈ 𝒯, θ ≠ trivialIrreducibleCharacter
      ↥((derivedInG hyp.base.T).subgroupOf hyp.base.T))
    (S : Set (ClassFunction ↥hyp.base.T ℂ))
    (hS : S = ↑(𝒯.image (fun θ => ClassFunction.induce
      ((derivedInG hyp.base.T).subgroupOf hyp.base.T) θ.toClassFunction)))
    (hyp07 : OddOrder.Peterfalvi.S07.Hypothesis
      (L := ↥hyp.base.T) (G := G) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (coh : OddOrder.Peterfalvi.S07.IsCoherent
      (tSideDadeMap hyp hG) S
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (OddOrder.BG.Ch4.S14.sigmaSharp hyp.base.T) hyp.base.T))
    (hirr : ∀ χ ∈ S, IsIrreducibleCharacter χ)
    {ζ : ClassFunction ↥hyp.base.T ℂ} (hζ : ζ ∈ S) :
    (coh.extension ζ).conj = coh.extension ζ.conj := by sorry

end OddOrder.Peterfalvi.S16
