-- Prove2me | Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
-- name    : IntMul.TrackedBankReservation.reserve_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:33:56.833262+00:00
-- url     : https://prove2.me/theorems/bdabfe2b-06e9-4e6b-a0d9-e6cfb931353e
-- title:
--   Actual fresh child-bank reservation preserving parent cells with exact maximum-distance clock
-- statement:
--   From a tracked parent frame whose heads are at most one past its visited extents and whose unvisited tails are genuinely blank, one fixed finite shared-tape routine physically finds every bank first fresh cell in exactly max_j(E_j+1-pos_j)+1 actual transitions. The full parent cells and all visited flags are unchanged; root input, caller buffer and their heads remain fixed; each work head is parked at oldOffset_j+E_j+1. Every suffix from that new physical boundary is fresh tagged blank, so child-bank reservation does not assume a free address oracle or free seek. The source proves the coarser max(E)+2 bound. Saved ancestor prefixes are retained; subsequent actual preparation writes child markers and copies the caller input.
-- source:
--   Original physical tracked fresh-suffix reservation for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedBankReservation
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)

open IntMul IntMul.TrackedBankReservation

theorem IntMul.TrackedBankReservation.reserve_correct (M : MultitapeTM) (base : (machine M).Cfg) (offset extent : Fin M.k → ℕ)
    (c : M.Cfg) (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank) :
    (machine M).step^[span M (distance M extent c.head) + 1] (initialFrame M base offset extent c) =
      finalFrame M base offset extent c ∧
    (∀ j p, newOffsets M offset extent j ≤ p →
      (finalFrame M base offset extent c).cells (workTape M j) p = some (M.blank,false)) ∧
    (∀ j, (finalFrame M base offset extent c).head (workTape M j) = newOffsets M offset extent j) := by sorry
