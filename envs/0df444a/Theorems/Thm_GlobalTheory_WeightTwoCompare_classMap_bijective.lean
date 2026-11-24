-- Prove2me | Theorems.Thm_GlobalTheory_WeightTwoCompare_classMap_bijective
-- name    : GlobalTheory.WeightTwoCompare.classMap_bijective
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:00.844913+00:00
-- url     : https://prove2.me/theorems/f46d71a0-a3ef-4334-85a1-8ae2985e548c
-- title:
--   Weight Two Compare: class Map bijective
-- statement:
--   The Weight Two Compare construction uses the class Map bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L114-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumDeformedLatticeEisensteinSummandWeightTwo.lean#L114-L143

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem GlobalTheory.WeightTwoCompare.classMap_bijective (𝔞 𝔟 : Frac (maximalRealSubfield E)) (θ : E) (L : Set E) (hθ : θ ∉ maximalRealSubfield E)
    (hL : ∀ x : E, x ∈ L ↔ ∃ a ∈ latM 𝔞, ∃ b ∈ (𝔟 : FractionalIdeal (𝓞 (maximalRealSubfield E))⁰ (maximalRealSubfield E)),
      x = (a : E) + (b : E) * θ) :
    Function.Bijective (classMap 𝔞 𝔟 θ L hθ hL) := by sorry
