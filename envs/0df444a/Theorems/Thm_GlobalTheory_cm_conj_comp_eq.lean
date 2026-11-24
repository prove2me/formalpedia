-- Prove2me | Theorems.Thm_GlobalTheory_cm_conj_comp_eq
-- name    : GlobalTheory.cm_conj_comp_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:34.694264+00:00
-- url     : https://prove2.me/theorems/09b8da1b-9b2b-409b-b968-333413f07428
-- title:
--   Global Theory: cm conj comp eq
-- statement:
--   The Global Theory construction uses the cm conj comp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldProdEmbeddingsRegroupMaximalReal.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CmFieldProdEmbeddingsRegroupMaximalReal.lean#L20-L25

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

theorem GlobalTheory.cm_conj_comp_eq (E : Type) [Field E] [NumberField E] (τ : E →+* ℂ) :
    (ComplexEmbedding.conjugate τ).comp (algebraMap (maximalRealSubfield E) E) =
      τ.comp (algebraMap (maximalRealSubfield E) E) := by sorry
