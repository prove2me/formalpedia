-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoCompare_hasSum_defTerm
-- name    : GlobalTheory.WeightTwoCompare.hasSum_defTerm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:52:00.157371+00:00
-- url     : https://prove2.me/theorems/ab9da980-70ce-47d9-bfe5-c242bec33a5a
-- title:
--   Weight Two Compare: has Sum def Term
-- statement:
--   The Weight Two Compare construction uses the has Sum def Term property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L149-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L149-L174

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DifferentiableRisingS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumDeformedLatticeEisensteinSummandWeightTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors
open GlobalTheory GlobalTheory.WeightTwoCompare

theorem GlobalTheory.WeightTwoCompare.hasSum_defTerm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ)
    (e : I ≃ Emb (maximalRealSubfield E)), (∀ (i : I) (a : maximalRealSubfield E), φ i (a : E) = ((e i a : ℝ) : ℂ)) →
    ∀ (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E), θ ∉ maximalRealSubfield E →
    (∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) →
    ∀ z ∈ polydisc I, ∀ (σ S : ℂ), HasSum (eisClass 𝔞 𝔟 2 σ (modPt φ e θ z)) S →
      HasSum (fun q : modUnits L => defTerm φ 2 z σ q.1.out) ((homFac z)⁻¹ ^ 2 * Complex.exp (-σ * logFac z) * S) := by sorry
