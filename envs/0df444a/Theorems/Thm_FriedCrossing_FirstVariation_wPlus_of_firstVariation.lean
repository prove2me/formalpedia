-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_wPlus_of_firstVariation
-- name    : FriedCrossing.FirstVariation.wPlus_of_firstVariation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:57:01.561941+00:00
-- url     : https://prove2.me/theorems/12a6e57d-39cb-5c64-bf5f-1c6655ce9db9
-- title:
--   First Variation: w Plus of first Variation
-- statement:
--   Over ℝ, with the rate oriented positive: the (4.22) matrix has w₊ = tr N = r₀ and w₋ = 0
--   in the notation of `TwinRate` — the two first-order rates of `twin_rate_of_cluster`.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L127-L131
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L127-L131

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.wPlus_of_firstVariation {Bcc Bcψ Bψc Bψψ p : ℝ}
    (hr : 0 < (Nmat Bcc Bcψ Bψc Bψψ p).trace) :
    TwinRate.wPlus (Nmat Bcc Bcψ Bψc Bψψ p).trace (Nmat Bcc Bcψ Bψc Bψψ p).det =
      (Nmat Bcc Bcψ Bψc Bψψ p).trace := by sorry
