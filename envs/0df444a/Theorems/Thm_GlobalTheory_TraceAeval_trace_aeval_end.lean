-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_end
-- name    : GlobalTheory.TraceAeval.trace_aeval_end
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:04.688389+00:00
-- url     : https://prove2.me/theorems/56178ab5-c91f-4deb-8a11-0d6a11ee3cea
-- title:
--   Trace Aeval: trace aeval end
-- statement:
--   The Trace Aeval construction uses the trace aeval end property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L36-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L36-L72

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

theorem GlobalTheory.TraceAeval.trace_aeval_end {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (f : Module.End ℂ V) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval f p) = (f.charpoly.roots.map fun z => p.eval z).sum := by sorry
