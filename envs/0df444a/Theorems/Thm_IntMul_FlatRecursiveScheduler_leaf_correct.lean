-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveScheduler_leaf_correct
-- name    : IntMul.FlatRecursiveScheduler.leaf_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T02:24:33.798771+00:00
-- url     : https://prove2.me/theorems/7b0d6b51-bf81-4932-9fe2-e4fde925f349
-- title:
--   Complete native leaf execution through one fixed-tape recursive scheduler
-- statement:
--   Suppose the body machine halts after T transitions on native input x#y with canonical result w and reaches no recursive request state before that halt. The same fixed-tape scheduler used for recursive calls runs from ordinary native input to canonical native output w. Its entire final configuration equals the native final frame: the input is retained, all work tapes and the continuation tape are fresh, work heads are parked, and the root continuation head is at its global marker. Writing L for input-word length, W for result length, H for the body output head at halt, P for the maximum relative head position after output rewind, and E for the maximum visited extent, the complete actual clock is at most T+5L+7W+max(H,1)+P+2E+30. Every initialization, copy, reset, body transition, return, cleanup, stack probe, output shift and dispatch is charged. This is the ordinary leaf case of the fixed scheduler; recursive execution induction and fast multiplication remain separate targets.
-- source:
--   Original complete native leaf execution for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveReturn
import Theorems.Thm_IntMul_FlatRecursiveScheduler_bootstrap_correct
import Theorems.Thm_IntMul_FlatRecursiveReturn_return_cleanup_correct
import Theorems.Thm_IntMul_TrackedBankedSimulation_simulate_run
import Theorems.Thm_IntMul_TrackedOutputShift_shift_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation IntMul.TrackedBankedSimulation IntMul.TrackedBankCleanup IntMul.FlatRecursiveReturn

theorem IntMul.FlatRecursiveScheduler.leaf_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (x y : List Bool) (T : ℕ) (halt : (M.step^[T] (M.initCfg x y)).state=M.qHalt)
    (no_request : ∀ s, s < T → request (M.step^[s] (M.initCfg x y)).state=none)
    (w : List Bool) (out : (M.step^[T] (M.initCfg x y)).cells M.outTape=M.tapeOf (w.map M.bitSym)) :
    let d := M.step^[T] (M.initCfg x y)
    let e := extents M (M.initCfg x y) (initialExtent M x y) T
    ∃ t, t ≤ T+5*(inputWord M x y).length+7*w.length+max (d.head M.outTape) 1+
        span M (returnedHeads M d)+2*span M e+30 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        nativeFinalFrame M n request resume x y w ∧
      (machine M n request resume).HaltsWithOutput x y t w := by sorry
