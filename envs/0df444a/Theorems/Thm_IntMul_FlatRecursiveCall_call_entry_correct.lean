-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveCall_call_entry_correct
-- name    : IntMul.FlatRecursiveCall.call_entry_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T02:30:12.692214+00:00
-- url     : https://prove2.me/theorems/03f40b8b-a515-4551-85c0-209b3621dc6c
-- title:
--   Complete physical recursive call entry on one depth-independent fixed-tape scheduler
-- statement:
--   A live body state requests a child invocation with a finite continuation label and a canonical request packet x#y. Its heads are within one cell of its visited extents, and every cell beyond those extents is blank. The actual single fixed-tape recursive scheduler copies that packet into the shared buffer while clearing any longer old result, physically saves the finite continuation label, reserves fresh suffixes on the same work tapes, prepares the child input, physically empties and rewinds the shared buffer, and enters the SAME original body control at the child start. The entire result equals the canonical child frame, retaining all saved parent and ancestor prefixes and the physical continuation record. Writing L=|x#y|, B=|v| for the older shared result, H for the parent output head, and D for the maximum reservation distance after output rewind, the actual clock is at most max(H,B+1)+2max(L,B)+3L+D+n+16. No depth, offset, length, extent or call tree occurs in delta. Parent resumption, recursive execution induction and fast multiplication remain separate targets.
-- source:
--   Original complete actual recursive call entry for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveCall
import Theorems.Thm_IntMul_TrackedChildInputBridge_input_correct
import Theorems.Thm_IntMul_TrackedBankReservation_reserve_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveCall IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation IntMul.TrackedBankCleanup

theorem IntMul.FlatRecursiveCall.call_entry_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (label : Fin n)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v x y : List Bool)
    (live : c.state≠M.qHalt) (call : request c.state=some label)
    (packet : c.cells M.outTape=M.tapeOf (inputWord M x y))
    (near : ∀ j, c.head j≤ extent j+1)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ max (c.head M.outTape) (v.length+1)+2*max (inputWord M x y).length v.length+
        3*(inputWord M x y).length+
        span M (TrackedBankReservation.distance M extent (parentAfterInput M c).head)+n+16 ∧
      (machine M n request resume).step^[t]
        (bodyFrame M n request resume base rho sigma offset extent c v)=
        childFrame M n request resume base rho sigma offset extent c label x y := by sorry
