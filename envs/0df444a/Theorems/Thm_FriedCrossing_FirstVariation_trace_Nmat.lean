-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat
-- name    : FriedCrossing.FirstVariation.trace_Nmat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:39:36.173962+00:00
-- url     : https://prove2.me/theorems/6b546ae7-0f38-43b1-a8a7-2d90969de17c
-- title:
--   First Variation: trace Nmat
-- statement:
--   The First Variation construction uses the trace Nmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L83-L88
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L83-L88

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.trace_Nmat (Bcc Bcψ Bψc Bψψ p : K) :
    (Nmat Bcc Bcψ Bψc Bψψ p).trace = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by sorry
