-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_powMat
-- name    : GlobalTheory.TraceAeval.trace_aeval_powMat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:10.975155+00:00
-- url     : https://prove2.me/theorems/b2850c5f-9d1a-4c21-9820-cdbdf54f271d
-- title:
--   Trace Aeval: trace aeval pow Mat
-- statement:
--   The Trace Aeval construction uses the trace aeval pow Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L126-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L126-L131

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

theorem GlobalTheory.TraceAeval.trace_aeval_powMat {ψ : ℤ[X]} (h : ψ.Monic) (p : ℤ[X]) :
    (((aeval (powMat ψ.natDegree ψ) p).trace : ℤ) : ℂ)
      = ((ψ.aroots ℂ).map fun z => aeval z p).sum := by sorry
