-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_trace_aeval_of_isNilpotent
-- name    : GlobalTheory.TraceAeval.trace_aeval_of_isNilpotent
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:07.585788+00:00
-- url     : https://prove2.me/theorems/df1f544e-ec51-49b2-9902-30e388f4802d
-- title:
--   Trace Aeval: trace aeval of is Nilpotent
-- statement:
--   The Trace Aeval construction uses the trace aeval of is Nilpotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L8-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L8-L22

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

theorem GlobalTheory.TraceAeval.trace_aeval_of_isNilpotent {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (g : Module.End ℂ V) (μ : ℂ) (h : IsNilpotent (g - algebraMap ℂ _ μ)) (p : ℂ[X]) :
    LinearMap.trace ℂ V (aeval g p) = (finrank ℂ V : ℂ) * p.eval μ := by sorry
