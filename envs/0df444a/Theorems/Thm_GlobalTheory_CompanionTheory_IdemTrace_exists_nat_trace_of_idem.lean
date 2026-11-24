-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IdemTrace_exists_nat_trace_of_idem
-- name    : GlobalTheory.CompanionTheory.IdemTrace.exists_nat_trace_of_idem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T11:47:51.152934+00:00
-- url     : https://prove2.me/theorems/19776ba3-18fe-4b55-9a34-029ec4f77d11
-- title:
--   Idem Trace: exists nat trace of idem
-- statement:
--   The Idem Trace construction uses the exists nat trace of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisible.lean#L5-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/TraceIdempotentNotDivisible.lean#L5-L47

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

theorem GlobalTheory.CompanionTheory.IdemTrace.exists_nat_trace_of_idem {O : Type} [CommRing O] [IsLocalRing O] {g : ℕ}
    (P : Matrix (Fin g) (Fin g) O) (h : P * P = P) :
    ∃ r : ℕ, r ≤ g ∧ Matrix.trace P = (r : O) ∧ (r = 0 → P = 0) := by sorry
