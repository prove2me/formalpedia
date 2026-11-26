-- Prove2me | Theorems.Thm_FriedCrossing_TorsionCore_dets_ne_zero
-- name    : FriedCrossing.TorsionCore.dets_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:54:22.556898+00:00
-- url     : https://prove2.me/theorems/245222d0-c6f3-4531-a64d-b40426727607
-- title:
--   Torsion Core: dets ne zero
-- statement:
--   The nondegeneracy that makes the (x, l)-complex EXACT: D₃, D₄ ≠ 0 ⟺ l ∉ {0, −x}
--   (memo: λ ∉ {0, −1} for the Jordan cluster).
--
--   Source: https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L94-L97
-- source:
--   https://github.com/blawton/fried-conj-lean/blob/610d659ea15af869553f6e3e79c432880d9b0ab0/B1s/fried_crossing_9_03.lean#L94-L97

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03
set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]

theorem FriedCrossing.TorsionCore.dets_ne_zero (x l : K) (hl : l ≠ 0) (hlx : l + x ≠ 0) :
    (D₂mat : Matrix (Fin 3) (Fin 3) K).det ≠ 0 ∧ (D₃mat x l).det ≠ 0 ∧ (D₄mat l).det ≠ 0 := by sorry
