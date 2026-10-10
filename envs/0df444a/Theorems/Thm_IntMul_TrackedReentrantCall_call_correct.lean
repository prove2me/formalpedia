-- Prove2me | Theorems.Thm_IntMul_TrackedReentrantCall_call_correct
-- name    : IntMul.TrackedReentrantCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T23:41:15.377755+00:00
-- url     : https://prove2.me/theorems/57ea18db-27ef-497c-af67-2860fd08eb75
-- title:
--   Complete physical child call preserving parent banks and restoring parent heads with explicit workspace cost
-- statement:
--   Let a tracked parent frame have bank offsets o_j, extents E_j, unique local markers, genuinely blank unvisited tails, and relative heads at most E_j+1. Suppose its caller buffer already contains x#y at boundary sigma, and a child halts after T steps with exact canonical output w. Write L=|x|+|y|+1, E_p=max_j E_j and E_c for the largest final tracked child extent. One fixed finite caller on the same k+2 tapes and finite alphabet performs the whole physical call with
--   \[t\le T+5E_c+2L+2E_p+19.\]
--   Its complete final configuration contains exactly w in the caller buffer with its head just after the output. Every parent bank cell and visited flag, including ancestor prefixes and blank tails, equals the starting frame, and every work head is physically returned to its retained parent boundary. Fresh suffixes are found by actual seeks; markers, input copying, tracked child steps, output return, full clearing, parent rewinds and both outer dispatches are all charged. No fresh address oracle or free head reset is assumed. The child-time coefficient is one, with child and parent workspace explicit. Caller input generation and unbounded recursive scheduling remain separate.
-- source:
--   Original complete physical reusable child call for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_TrackedReentrantCall
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankedCall_call_correct
import Theorems.Thm_IntMul_TrackedParentRestore_restore_correct
import Mathlib.Tactic
open IntMul.BankedSimulation (workTape)
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

open IntMul IntMul.TrackedReentrantCall

theorem IntMul.TrackedReentrantCall.call_correct (M : MultitapeTM) (base : (machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : base.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : base.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 19 ∧
      (machine M).step^[t] (initialFrame M base offset extent c) =
        finalFrame M base sigma offset extent c x y T w ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).cells (workTape M j) =
        (initialFrame M base offset extent c).cells (workTape M j)) ∧
      (∀ j, ((machine M).step^[t] (initialFrame M base offset extent c)).head (workTape M j) = offset j) ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).cells ⟨1,by change 1 < M.k + 2; omega⟩ =
        TrackedOutputReturn.bufferTape M (base.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M).step^[t] (initialFrame M base offset extent c)).head ⟨1,by change 1 < M.k + 2; omega⟩ =
        sigma + w.length + 1 := by sorry
