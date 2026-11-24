-- Prove2me | Theorems.Thm_GlobalTheory_LogCompress_trace_log_le_log_det
-- name    : GlobalTheory.LogCompress.trace_log_le_log_det
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:16:50.805139+00:00
-- url     : https://prove2.me/theorems/54263b62-a986-47b5-9f0e-7ef8f32623f9
-- title:
--   Log Compress: trace log le log det
-- statement:
--   The Log Compress construction uses the trace log le log det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L64-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TraceLogLeLogDet.lean#L64-L119

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TraceLogLeLogDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.LogCompress

theorem GlobalTheory.LogCompress.trace_log_le_log_det : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (H A : Matrix ι ι ℂ) (Q : Matrix ι κ ℂ), IsLog H A → Qᴴ * Q = 1 → (Matrix.trace (Qᴴ * H * Q)).re ≤ Real.log (Qᴴ * A * Q).det.re ∧ ((Matrix.trace (Qᴴ * H * Q)).re = Real.log (Qᴴ * A * Q).det.re → ∃ N : Matrix κ κ ℂ, A * Q = Q * N) := by sorry
