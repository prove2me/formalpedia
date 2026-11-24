-- Prove2me | Theorems.Thm_GlobalTheory_T_trace_idempotent_not_divisible
-- name    : GlobalTheory.T.trace_idempotent_not_divisible
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:52.069983+00:00
-- url     : https://prove2.me/theorems/c4887b2e-b8f1-49c3-8522-a235042f7bdc
-- title:
--   T: trace idempotent not divisible
-- statement:
--   The T construction uses the trace idempotent not divisible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisibleStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisibleStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisibleStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.trace_idempotent_not_divisible : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B) (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m → x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} → ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by sorry
