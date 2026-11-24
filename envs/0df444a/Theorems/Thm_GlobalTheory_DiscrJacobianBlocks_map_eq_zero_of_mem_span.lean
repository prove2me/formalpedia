-- Prove2me | Theorems.Thm_GlobalTheory_DiscrJacobianBlocks_map_eq_zero_of_mem_span
-- name    : GlobalTheory.DiscrJacobianBlocks.map_eq_zero_of_mem_span
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:50:58.298233+00:00
-- url     : https://prove2.me/theorems/9fd5fd79-30f3-402f-a4a5-5b0246e83c3b
-- title:
--   Discr Jacobian Blocks: map eq zero of mem span
-- statement:
--   The Discr Jacobian Blocks construction uses the map eq zero of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/ExistsFactorAssociatedJacobian.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DiscrEqJacobianOfIntegralPointsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsFactorAssociatedJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.DiscrJacobianBlocks

theorem GlobalTheory.DiscrJacobianBlocks.map_eq_zero_of_mem_span {O A ι : Type} [CommRing O] [CommRing A] [Algebra O A]
    (e : A →ₐ[O] O) (F : ι → A) (h : ∀ i, e (F i) = 0) {G : A}
    (hG : G ∈ Ideal.span (Set.range F)) : e G = 0 := by sorry
