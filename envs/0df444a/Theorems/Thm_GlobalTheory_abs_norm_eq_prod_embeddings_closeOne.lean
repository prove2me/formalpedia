-- Prove2me | Theorems.Thm_GlobalTheory_abs_norm_eq_prod_embeddings_closeOne
-- name    : GlobalTheory.abs_norm_eq_prod_embeddings_closeOne
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:04:28.508426+00:00
-- url     : https://prove2.me/theorems/304e40f7-fae0-412f-a746-6f2edd7c5651
-- title:
--   Global Theory: abs norm eq prod embeddings close One
-- statement:
--   The Global Theory construction uses the abs norm eq prod embeddings close One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqOneOfNormOneValuationSubOneSmall.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/EqOneOfNormOneValuationSubOneSmall.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_EqOneOfNormOneValuationSubOneSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory

theorem GlobalTheory.abs_norm_eq_prod_embeddings_closeOne {E : Type} [Field E] [NumberField E] (x : E) :
    |((Algebra.norm ℚ x : ℚ) : ℝ)| = ∏ σ : E →+* ℂ, ‖σ x‖ := by sorry
