-- Prove2me | Theorems.Thm_GlobalTheory_TraceAeval_charpoly_powMat
-- name    : GlobalTheory.TraceAeval.charpoly_powMat
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:11:11.98481+00:00
-- url     : https://prove2.me/theorems/ca16b76e-0b1f-4895-915d-941becfef0d5
-- title:
--   Trace Aeval: charpoly pow Mat
-- statement:
--   The Trace Aeval construction uses the charpoly pow Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L107-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TracePowerSumModEq.lean#L107-L124

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

theorem GlobalTheory.TraceAeval.charpoly_powMat {ψ : ℂ[X]} (h : ψ.Monic) : (powMat ψ.natDegree ψ).charpoly = ψ := by sorry
