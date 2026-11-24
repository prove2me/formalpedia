-- Prove2me | Theorems.Thm_GlobalTheory_TraceExpSmul_trace_R_mul_pow_eq_zero
-- name    : GlobalTheory.TraceExpSmul.trace_R_mul_pow_eq_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:51.256581+00:00
-- url     : https://prove2.me/theorems/6f7e9354-0268-42a8-bb5d-b4c0cfa592c8
-- title:
--   Trace Exp Smul: trace R mul pow eq zero
-- statement:
--   The Trace Exp Smul construction uses the trace R mul pow eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceRMulPowEqZero.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/TraceRMulPowEqZero.lean#L30-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_TraceRMulPowEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TraceExpSmul
open Finset
variable {K : Type*} {n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem GlobalTheory.TraceExpSmul.trace_R_mul_pow_eq_zero {R N : Matrix n n K} (hN : IsNilpotent N) {d : K}
    (h : N * R = d • (R * N)) (k : ℕ) (hk : 1 ≤ k) : Matrix.trace (R * N ^ k) = 0 := by sorry
