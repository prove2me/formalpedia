-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_S
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.induce_H_mem_zSpan_S
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:42:55.596379+00:00
-- url     : https://prove2.me/theorems/593a9b09-8929-4075-a43f-0ea11c6f2ee2
-- title:
--   Peterfalvi (13.5): induced characters of $H=PC$ with $P\not\subseteq\ker\theta$ lie in $\mathbb Z[\mathcal S]$
-- statement:
--   Let $G$ be a finite minimal simple group of odd order and `hyp : Hypothesis (G := G)` the Peterfalvi Section 13 hypothesis package, with subgroups $H,P\le S\le G$, and let `chief` be a chief-factor datum for the associated Types I--V setup of $S$. Let $\theta$ be an irreducible character of $H$ (as a subgroup of $S$) such that $P$ is not contained in the kernel of $\theta$. Then
--   $$\mathrm{Ind}_H^{S}\theta\ \in\ \mathbb Z[\mathcal S],$$
--   the $\mathbb Z$-span (`zSpan`) of the family $\mathcal S$ of Section 9 (taken from `mkSection11CharacterDataS_honest`).
--
--   This is the family membership underlying the Peterfalvi (13.5) preamble, used throughout the Section 13 character computations.
--
--   **Formalization Note.** The subgroups $H,P$ are viewed inside `↥S` via `subgroupOf`; the statement is formulated for the scoped `FiniteInduce` instances.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CaseACoherence.lean#L1024-L1156

import Definitions.Def_OddOrder_Peterfalvi_S15_NineElevenSevenEight
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_MuColumnPin
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_DegreesFirstSplit
import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped FiniteInduce in

theorem Hypothesis.induce_H_mem_zSpan_S [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetupS hG))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan (hyp.mkSection11CharacterDataS_honest hG chief).S := by sorry

end OddOrder.Peterfalvi.S15
