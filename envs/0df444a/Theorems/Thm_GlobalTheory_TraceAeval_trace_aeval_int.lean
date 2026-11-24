-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_int
-- name    : GlobalTheory.TraceAeval.trace_aeval_int
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:55.410749+00:00
-- url     : https://prove2.me/theorems/a86b4d17-82f2-45a0-bfa5-d847fc28e032
-- title:
--   Trace Aeval: trace aeval int
-- statement:
--   The Trace Aeval construction uses the trace aeval int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L88-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L88-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TracePowerSumModEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.TraceAeval
open Module

theorem GlobalTheory.TraceAeval.trace_aeval_int {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (p : ℤ[X]) :
    (((aeval A p).trace : ℤ) : ℂ)
      = ((A.map (Int.castRingHom ℂ)).charpoly.roots.map fun z => aeval z p).sum := by sorry
