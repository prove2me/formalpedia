-- Prove2me | Theorems.Thm_IntMul_TrackedNativeCall_call_correct
-- name    : IntMul.TrackedNativeCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:21:59.811636+00:00
-- url     : https://prove2.me/theorems/3aabbbf5-10c7-4cc5-be9c-0616d0113e9e
-- title:
--   Native child execution with exact canonical output and reusable fresh work banks, charging every phase
-- statement:
--   For any finite child M, real native input x#y, child halt clock T and exact canonical child output w, the constructed single finite M.k+2-tape caller halts from its own native initCfg with exactly w at the native output origin, in at most T+5E+4L+4length(w)+24 actual transitions, where L=length(x)+length(y)+1 and E is the largest final tracked child extent. Every child work bank is completely fresh tagged blank from cell one onward and its head is parked at one. Input production, all local markers and visited flags, setup/erase/rewinds, tracked execution, output return, complete cleanup, native output shift, and every inner/outer dispatch are physical and charged. The child-time coefficient is one; child workspace stays explicit. Root input cells and global markers are preserved. This does not assume a prepared input or free fresh-bank allocation and does not itself implement unbounded recursion.
-- source:
--   Original complete physical native caller and fresh-bank return compiler for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedNativeCall
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Mathlib.Data.List.GetD
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

open IntMul IntMul.TrackedNativeCall

theorem IntMul.TrackedNativeCall.call_correct (M : MultitapeTM) (x y : List Bool) (T : ℕ)
    (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        4 * (inputWord M x y).length + 4 * w.length + 24 ∧
      (machine M).HaltsWithOutput x y t w ∧
      (∀ j p, 1 ≤ p → ((machine M).step^[t] ((machine M).initCfg x y)).cells (BankedSimulation.workTape M j) p =
        some (M.blank,false)) ∧
      (∀ j, ((machine M).step^[t] ((machine M).initCfg x y)).head (BankedSimulation.workTape M j) = 1) := by sorry
