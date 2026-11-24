-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdemTrace_not_dvd_trace
-- name    : GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:47.452891+00:00
-- url     : https://prove2.me/theorems/845a82d0-9a9d-4007-a83c-0d55b41f6b97
-- title:
--   Idem Trace: not dvd trace
-- statement:
--   The Idem Trace construction uses the not dvd trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisible.lean#L67-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisible.lean#L67-L125

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_TraceIdempotentNotDivisible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IdemTrace

theorem GlobalTheory.CompanionTheory.IdemTrace.not_dvd_trace : ∀ (B : Type) [CommRing B] [Module.Free ℤ B] [Module.Finite ℤ B] (x : B)
    (p m : ℕ), p.Prime → Module.finrank ℤ B < p ^ m →
    x * x - x ∈ Ideal.span {((p : B)) ^ m} → x ∉ Ideal.span {((p : B)) ^ m} →
    ¬ ((p : ℤ) ^ m ∣ Algebra.trace ℤ B x) := by sorry
