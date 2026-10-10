-- Prove2me | Theorems.Thm_IntMul_SavedContinuationCall_call_correct
-- name    : IntMul.SavedContinuationCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T00:11:09.455603+00:00
-- url     : https://prove2.me/theorems/62631b29-f3db-4131-a50d-41a6a347650c
-- title:
--   Complete physical child call with saved return-control recovery, exact parent preservation and stack restoration
-- statement:
--   Suppose a tracked parent has unique local markers and genuinely blank unvisited tails, and its caller buffer already physically holds the child packet x#y. Let T be a child halt clock with exact canonical output w, L=|x|+|y|+1, E_p the largest parent extent, E_c the largest final tracked child extent, and n the fixed number of continuation labels. For any saved finite return label q and arbitrary older stack prefix, one fixed finite shared-tape caller completes the physical call with
--   \[t\le T+5E_c+2L+2E_p+2n+24.\]
--   Its finite control contains the recovered label q; every parent bank cell and visited flag is retained; parent heads return to their local boundaries; the caller buffer contains exactly w with its head just after the output; the stack head is restored to its boundary and the entire continuation record is erased to its original fresh suffix. The complete final configuration is exact. Every continuation write/read/erase, fresh-bank seek, marker and input copy, child step, output return, cleanup, parent rewind and outer dispatch is an actual charged transition. The same finite alphabet and k+3 tapes work at arbitrary older stack depths. Caller input generation and a full unbounded recursive multiplication scheduler remain separate work.
-- source:
--   Original complete physical saved-continuation child caller for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_SavedContinuationCall
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Theorems.Thm_IntMul_TrackedReentrantCall_call_correct
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)
open IntMul.TrackedBankPreparation (inputWord initialExtent)

open IntMul IntMul.SavedContinuationCall

theorem IntMul.SavedContinuationCall.call_correct (M : MultitapeTM) (n : ℕ) (initial : Fin n)
    (base : (machine M n initial).Cfg) (rho : ℕ) (q : Fin n) (parent : (TrackedReentrantCall.machine M).Cfg) (sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (x y : List Bool)
    (source : parent.cells ⟨1,by change 1 < M.k + 2; omega⟩ =
      TrackedBankPreparation.sourceTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma (inputWord M x y))
    (source_head : parent.head ⟨1,by change 1 < M.k + 2; omega⟩ = sigma)
    (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    ∃ t, t ≤ T + 5 * span M (extents M (M.initCfg x y) (initialExtent M x y) T) +
        2 * (inputWord M x y).length + 2 * span M extent + 2 * n + 24 ∧
      (machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c) =
        callFinalFrame M n initial base rho q parent sigma offset extent c x y T w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).state =
        .inr (.inr (.resume q)) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FiniteContinuationStack.stackTape M) =
          FiniteContinuationStack.freshTape M (base.cells (FiniteContinuationStack.stackTape M)) rho ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FiniteContinuationStack.stackTape M) = rho ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) =
        (TrackedReentrantCall.initialFrame M parent offset extent c).cells (BankedSimulation.workTape M j)) ∧
      (∀ j, ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) (BankedSimulation.workTape M j)) = offset j) ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).cells
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
        TrackedOutputReturn.bufferTape M (parent.cells ⟨1,by change 1 < M.k + 2; omega⟩) sigma w ∧
      ((machine M n initial).step^[t] (callInitialFrame M n initial base rho q parent offset extent c)).head
        (FixedTapeExtension.oldTape (TrackedReentrantCall.machine M) ⟨1,by change 1 < M.k + 2; omega⟩) =
          sigma + w.length + 1 := by sorry
