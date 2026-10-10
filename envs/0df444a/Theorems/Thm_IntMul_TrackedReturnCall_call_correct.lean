-- Prove2me | Theorems.Thm_IntMul_TrackedReturnCall_call_correct
-- name    : IntMul.TrackedReturnCall.call_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T22:36:26.937069+00:00
-- url     : https://prove2.me/theorems/875aec6c-afc8-465b-80d9-e69c4dd89161
-- title:
--   Complete fixed-tape child execution, output return and fresh-bank cleanup with charged finite dispatches
-- statement:
--   For a finite child M with prepared tracked banks and empty local caller buffer, unique local markers, initialized blank tails and heads at most one past the visited extents, any child halt clock T with canonical output w yields a full outer run that returns w and clears all child banks for reuse. If d and e are the child's T-step configuration and final tracked extents, its cost is at most T+max(bufferDistance,d.outputHead)+length(w)+max(postCopyHeadDistances)+2*max(e)+7. Both first-halt stage dispatches are physically charged and padded child clocks preserve exact terminal flags. The final buffer holds the exact output and blank tail; root input and all ancestor prefixes are retained; all child bank suffixes and temporary markers are fresh blank and work heads are parked at their original offsets. Workspace remains explicit, keeping coefficient one on child execution time. Preparation and unbounded recursion are separate obligations.
-- source:
--   Original fixed-state-sum child/output/cleanup compiler for the integer-multiplication campaign. Written by Codex.

import Definitions.Def_IntMul_TrackedReturnCall
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedOutputReturn_output_correct
import Theorems.Thm_IntMul_TrackedBankCleanup_cleanup_correct
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic
open IntMul.TrackedBankCleanup (span)
open IntMul.TrackedBankedSimulation (extents)

open IntMul IntMul.TrackedReturnCall

theorem IntMul.TrackedReturnCall.call_correct (M : MultitapeTM) (base : (machine M).Cfg)
    (sigma a : ℕ) (offset extent : Fin M.k → ℕ) (positive : ∀ j, 1 ≤ offset j)
    (c : M.Cfg) (T : ℕ) (unique : ∀ j p, c.cells j p = M.startSym ↔ p = 0)
    (tail : ∀ j p, extent j < p → c.cells j p = M.blank)
    (near : ∀ j, c.head j ≤ extent j + 1)
    (halt : (M.step^[T] c).state = M.qHalt)
    (w : List Bool) (out : (M.step^[T] c).cells M.outTape = M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] c
    let e := extents M c extent T
    ∃ t, t ≤ T + max a (d.head M.outTape) + w.length + span M (postCopyHeads M d w) + 2 * span M e + 7 ∧
      (machine M).step^[t] (initialFrame M base sigma a offset extent c) =
        finalFrame M base sigma offset e d w := by sorry
