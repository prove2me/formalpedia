-- Prove2me | Theorems.Thm_GlobalTheory_ideal_span_natCast_smul_top_eq_range
-- name    : GlobalTheory.ideal_span_natCast_smul_top_eq_range
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:47.684318+00:00
-- url     : https://prove2.me/theorems/00b34a54-29bc-4a08-8a94-b923357bce02
-- title:
--   Global Theory: ideal span nat Cast smul top eq range
-- statement:
--   The Global Theory construction uses the ideal span nat Cast smul top eq range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L6-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CardZmodTensorEqCardQuotPrimeMultiples.lean#L6-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardZmodTensorEqCardQuotPrimeMultiples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.ideal_span_natCast_smul_top_eq_range (M : Type) [AddCommGroup M] [Module ℤ M] (p : ℕ) :
    (Ideal.span {(p : ℤ)}) • (⊤ : Submodule ℤ M) =
      LinearMap.range ((p : ℤ) • (LinearMap.id : M →ₗ[ℤ] M)) := by sorry
