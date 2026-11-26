-- Prove2me | Theorems.Thm_GlobalTheory_factorial_mul_pow_mono
-- name    : GlobalTheory.factorial_mul_pow_mono
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:47:08.733488+00:00
-- url     : https://prove2.me/theorems/013be84b-6247-420c-a7a2-e3cc3b5b6d39
-- title:
--   Global Theory: factorial mul pow mono
-- statement:
--   The Global Theory construction uses the factorial mul pow mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L298-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/FormPerpVectorMemOfIntegral.lean#L298-L300

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

theorem GlobalTheory.factorial_mul_pow_mono {p N : ℕ} (hp : p ≤ N) {r : ℝ} (hr : 1 ≤ r) :
    ((p + 1)! : ℝ) * r ^ (2 * p + 1) ≤ (N + 1)! * r ^ (2 * N + 1) := by sorry
