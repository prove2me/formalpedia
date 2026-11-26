-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_charpoly_roots
-- name    : FriedCrossing.FirstVariation.charpoly_roots
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:56:51.598931+00:00
-- url     : https://prove2.me/theorems/2332dc99-d1aa-52a6-8e6e-cb07a5ce97c8
-- title:
--   First Variation: charpoly roots
-- statement:
--   The eigenvalues of ∂_τZ(0) on Res¹₀ are exactly 0 (the closed state, frozen) and
--   B_cc·p/det B (the non-closed state): z is a root of the characteristic polynomial iff so.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L95-L107
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L95-L107

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.charpoly_roots (Bcc Bcψ Bψc Bψψ p : K) (z : K) :
    z ^ 2 - (Nmat Bcc Bcψ Bψc Bψψ p).trace * z + (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 ↔
      z = 0 ∨ z = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by sorry
