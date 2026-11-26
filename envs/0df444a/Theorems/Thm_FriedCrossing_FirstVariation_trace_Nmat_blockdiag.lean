-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat_blockdiag
-- name    : FriedCrossing.FirstVariation.trace_Nmat_blockdiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:57:00.394638+00:00
-- url     : https://prove2.me/theorems/c1c41de8-d1ae-445f-9238-e1b8a4bc0f0d
-- title:
--   First Variation: trace Nmat blockdiag
-- statement:
--   CDDP (3.55)–(3.56): the pairing is block diagonal across C × C_ψ*, so the rate is p/B_ψψ.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L110-L114
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L110-L114

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.trace_Nmat_blockdiag {Bcc Bψψ p : K} (hcc : Bcc ≠ 0) (hψψ : Bψψ ≠ 0) :
    (Nmat Bcc 0 0 Bψψ p).trace = p / Bψψ := by sorry
