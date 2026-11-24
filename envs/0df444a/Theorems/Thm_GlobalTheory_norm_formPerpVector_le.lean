-- Prove2me | Theorems.Thm_GlobalTheory_norm_formPerpVector_le
-- name    : GlobalTheory.norm_formPerpVector_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:13:08.229329+00:00
-- url     : https://prove2.me/theorems/79267c59-abe1-4537-beba-cf334034509c
-- title:
--   Global Theory: norm form Perp Vector le
-- statement:
--   The Global Theory construction uses the norm form Perp Vector le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L321-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L321-L326

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

theorem GlobalTheory.norm_formPerpVector_le {p : ℕ} (e e' : Fin p → V) (g : V) {r : ℝ} (he : ∀ a, ‖e a‖ ≤ r)
    (he' : ∀ a, ‖e' a‖ ≤ r) (hg : ‖g‖ ≤ r) :
    ‖formPerpVector (innerFormLeft V) e e' g‖ ≤ (p + 1)! * r ^ (2 * p + 1) := by sorry
