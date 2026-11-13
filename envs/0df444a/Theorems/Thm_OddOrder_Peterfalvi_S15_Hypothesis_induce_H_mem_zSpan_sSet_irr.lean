-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S15_Hypothesis_induce_H_mem_zSpan_sSet_irr
-- name    : OddOrder.Peterfalvi.S15.Hypothesis.induce_H_mem_zSpan_sSet_irr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T16:54:31.747114+00:00
-- url     : https://prove2.me/theorems/ab147707-db6b-4ae2-aeeb-232190fe4bcc
-- title:
--   Irreducible induced characters from $H=PC$ lie in the $\mathbb Z$-span of the irreducible members of $\mathcal S$
-- statement:
--   Let $G$ be a finite group with `IsMinimalSimpleOdd G` and `hyp : Hypothesis` the Peterfalvi (13.1) configuration, with $H=PC\le S$. Let $\theta$ be an irreducible character of $H$ (as a subgroup of $S$) with $P\not\subseteq\ker\theta$, and assume the induced character $\mathrm{Ind}_H^S\theta$ is irreducible. Then
--
--   $$\mathrm{Ind}_H^S\theta\ \in\ \mathbb Z\text{-span}\{\psi\ :\ \psi\in\mathcal S,\ \psi\text{ irreducible character of }S\},$$
--
--   where $\mathcal S=$ `sSet (hyp.toTypesIIIIIIVSetupS hG)` is the family of Section 9 for $S$ and the span is the integral span `zSpan`.
--
--   This is the irreducible branch of the `S1cases` statement of the Coq development; it is used in the Case B degree analysis for $S$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S15_CharacterDegreeEnginesSSide.lean#L42-L259

import Definitions.Def_OddOrder_Peterfalvi_S15_CaseACoherence
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_CountingLayer
import Definitions.Def_OddOrder_Peterfalvi_S15_SAndT_Setup_TSideDegrees
import Definitions.Def_OddOrder_Peterfalvi_S15_Tau1T
import Definitions.Def_OddOrder_Peterfalvi_S15_CharacterDegreeEnginesSSide

namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

variable {G : Type*} [Group G]

set_option maxHeartbeats 800000 in
-- raised heartbeat budget for the heavy elaboration below
open OddOrder.Peterfalvi.S11 in
open scoped FiniteInduce in

theorem Hypothesis.induce_H_mem_zSpan_sSet_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis (G := G))
    (θ : ClassFunction ↥(hyp.H.subgroupOf hyp.S) ℂ)
    (hθ : OddOrder.RepresentationTheory.IsIrreducibleCharacter θ)
    (hθP : ¬ (((hyp.P.subgroupOf hyp.S).subgroupOf (hyp.H.subgroupOf hyp.S) :
        Set ↥(hyp.H.subgroupOf hyp.S)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel θ))
    (hind : OddOrder.RepresentationTheory.IsIrreducibleCharacter
      (ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ)) :
    ClassFunction.induce (hyp.H.subgroupOf hyp.S) θ ∈
      OddOrder.Peterfalvi.S07.zSpan
        {ψ : ClassFunction ↥hyp.S ℂ | ψ ∈ sSet (hyp.toTypesIIIIIIVSetupS hG) ∧
          OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ} := by sorry

end OddOrder.Peterfalvi.S15
