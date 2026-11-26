-- Prove2me | Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat_ne_zero_iff
-- name    : FriedCrossing.FirstVariation.trace_Nmat_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:56:57.725797+00:00
-- url     : https://prove2.me/theorems/65e6c3f3-ac6b-4fd1-80e2-6261d487e00a
-- title:
--   First Variation: trace Nmat ne zero iff
-- statement:
--   The non-closed rate is non-zero iff p ≠ 0: CDDP's non-degeneracy (1.3) ⟺ r₀ ≠ 0.
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L117-L123
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_firstvariation_9_08.lean#L117-L123

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]

theorem FriedCrossing.FirstVariation.trace_Nmat_ne_zero_iff {Bcc Bcψ Bψc Bψψ p : K} (hcc : Bcc ≠ 0)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    (Nmat Bcc Bcψ Bψc Bψψ p).trace ≠ 0 ↔ p ≠ 0 := by sorry
