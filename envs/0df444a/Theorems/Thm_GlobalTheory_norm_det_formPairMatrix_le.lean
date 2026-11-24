-- Prove2me | Theorems.Thm_GlobalTheory_norm_det_formPairMatrix_le
-- name    : GlobalTheory.norm_det_formPairMatrix_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:12:14.842966+00:00
-- url     : https://prove2.me/theorems/29aa8163-bd40-487a-aa98-7d196c205ddf
-- title:
--   Global Theory: norm det form Pair Matrix le
-- statement:
--   The Global Theory construction uses the norm det form Pair Matrix le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L315-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L315-L319

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_FormPerpVectorMemOfIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Nat
open GlobalTheory
variable {V : Type*} [SeminormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem GlobalTheory.norm_det_formPairMatrix_le {p : ℕ} (e e' : Fin p → V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) :
    ‖(formPairMatrix (innerFormLeft V) e e').det‖ ≤ p ! * r ^ (2 * p) := by sorry
