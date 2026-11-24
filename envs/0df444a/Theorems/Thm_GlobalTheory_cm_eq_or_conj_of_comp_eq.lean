-- Prove2me | Theorems.Thm_GlobalTheory_cm_eq_or_conj_of_comp_eq
-- name    : GlobalTheory.cm_eq_or_conj_of_comp_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:38.218715+00:00
-- url     : https://prove2.me/theorems/6c6602c4-07d8-4c38-a6e5-c2023924e532
-- title:
--   Global Theory: cm eq or conj of comp eq
-- statement:
--   The Global Theory construction uses the cm eq or conj of comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldProdEmbeddingsRegroupMaximalReal.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldProdEmbeddingsRegroupMaximalReal.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldProdEmbeddingsRegroupMaximalReal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.cm_eq_or_conj_of_comp_eq (E : Type) [Field E] [NumberField E] [IsCMField E]
    (τ τ' : E →+* ℂ)
    (h : τ'.comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E)) :
    τ' = τ ∨ τ' = ComplexEmbedding.conjugate τ := by sorry
