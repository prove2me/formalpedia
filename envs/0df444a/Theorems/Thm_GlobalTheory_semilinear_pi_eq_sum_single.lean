-- Prove2me | Theorems.Thm_GlobalTheory_semilinear_pi_eq_sum_single
-- name    : GlobalTheory.semilinear_pi_eq_sum_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:29:52.33379+00:00
-- url     : https://prove2.me/theorems/a786c448-6308-4d5c-a406-4639779395e8
-- title:
--   Global Theory: semilinear pi eq sum single
-- statement:
--   The Global Theory construction uses the semilinear pi eq sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanRangeInfKerEqSpanRationalKer.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpanRangeInfKerEqSpanRationalKer.lean#L7-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanRangeInfKerEqSpanRationalKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory

theorem GlobalTheory.semilinear_pi_eq_sum_single {K : Type} [Field K] (σ : K →+* ℂ) {W : Type} [AddCommGroup W]
    [Module ℂ W] {n : ℕ} (j : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    j x = ∑ k, σ (x k) • j (Pi.single k 1) := by sorry
