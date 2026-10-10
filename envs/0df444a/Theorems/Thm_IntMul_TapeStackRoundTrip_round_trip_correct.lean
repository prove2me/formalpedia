-- Prove2me | Theorems.Thm_IntMul_TapeStackRoundTrip_round_trip_correct
-- name    : IntMul.TapeStackRoundTrip.round_trip_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T21:48:20.934978+00:00
-- url     : https://prove2.me/theorems/c53378f5-4662-4bab-bd49-b297c422983b
-- title:
--   Complete physical stack push/pop round trip with restored tapes and charged dispatch
-- statement:
--   For every saved configuration, local source/stack/scratch boundaries and binary word w, one fixed seventeen-state four-tape caller pushes and erases w, physically dispatches to pop, restores w in its original order, erases parked and temporary suffixes, restores every local head and globally halts within 5|w|+9 transitions. The full final frame is proved, and all initial tape contents and head positions are restored. The bound is independent of older stack prefix size and number of ancestors. Prepared source/local separators/fresh suffixes are explicit preconditions; buffer production, allocation and recursive scheduler integration remain separate tasks.
-- source:
--   Original actual one-way MultitapeTM formalization of the fixed-control stack push/pop strategy in CrocSwap/integer-mult-bounds research/machine-transfer-verification/transfer-proof/tapes/TapeStack*.lean, pinned at 3b6b66891c0ac888521cf591fe306c6286601d4f. Written by Codex.

import Definitions.Def_IntMul_TapeStackRoundTrip
import Theorems.Thm_IntMul_FiniteCaller_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.TapeStackRoundTrip

theorem IntMul.TapeStackRoundTrip.round_trip_correct (base : TapeStack.machine.Cfg) (sigma rho tau : ℕ) (w : List Bool) :
    ∃ t : ℕ, t ≤ 5 * w.length + 9 ∧
      machine.step^[t] (initialFrame base sigma rho tau w) = finalFrame base sigma rho tau w := by sorry
