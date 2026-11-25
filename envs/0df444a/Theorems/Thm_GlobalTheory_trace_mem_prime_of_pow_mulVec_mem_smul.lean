-- Prove2me | Theorems.Thm_GlobalTheory_trace_mem_prime_of_pow_mulVec_mem_smul
-- name    : GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:51:14.496804+00:00
-- url     : https://prove2.me/theorems/d6d4813f-1414-5147-9548-941a586c228c
-- title:
--   Global Theory: trace mem prime of pow mul Vec mem smul
-- statement:
--   The Global Theory construction uses the trace mem prime of pow mul Vec mem smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/TraceMemPrimeOfPowMulVecMemSmul.lean#L37-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/TraceMemPrimeOfPowMulVecMemSmul.lean#L37-L128

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_TraceMemPrimeOfPowMulVecMemSmul
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
open NumberField Polynomial Matrix

theorem GlobalTheory.trace_mem_prime_of_pow_mulVec_mem_smul : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (L : Submodule (𝓞 K) (Fin r → K))
      (N : Matrix (Fin r) (Fin r) K) (P : Ideal (𝓞 K)) (n : ℕ), L.FG →
      Submodule.span K (L : Set (Fin r → K)) = ⊤ → P.IsPrime → (∀ x ∈ L, N.mulVec x ∈ L) →
      (∀ x ∈ L, (N ^ n).mulVec x ∈ P • L) → ∃ z ∈ P, ((z : 𝓞 K) : K) = N.trace := by sorry
