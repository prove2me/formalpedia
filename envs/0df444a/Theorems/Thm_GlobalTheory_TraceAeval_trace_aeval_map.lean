-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_map
-- name    : GlobalTheory.TraceAeval.trace_aeval_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:52.774031+00:00
-- url     : https://prove2.me/theorems/6a49cbc9-9560-4fa6-b6fb-09d1216bb8e8
-- title:
--   Trace Aeval: trace aeval map
-- statement:
--   The Trace Aeval construction uses the trace aeval map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L80-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L80-L86

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

theorem GlobalTheory.TraceAeval.trace_aeval_map {n : ℕ} {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) ℤ)
    (p : ℤ[X]) :
    (aeval (A.map (Int.castRingHom R)) p).trace = (((aeval A p).trace : ℤ) : R) := by sorry
