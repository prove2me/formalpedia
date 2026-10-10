-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveResume_resume_parent_correct
-- name    : IntMul.FlatRecursiveResume.resume_parent_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T02:44:29.409413+00:00
-- url     : https://prove2.me/theorems/59d04d22-37ac-4fcf-9e5f-7daef568ca21
-- title:
--   Complete physical parent resumption on one depth-independent fixed-tape scheduler
-- statement:
--   The actual child has returned and completely cleared its own work banks on the single fixed-tape recursive scheduler. The saved parent has unique local markers and blank tails beyond its visited extents. The scheduler physically reads the last saved continuation bit, moves the stack head right, restores every parent work head to its original marker, pops and recovers the finite continuation label while restoring the earlier stack prefix, places the returned word into the parent output bank while erasing excess old tail, and enters the SAME original body control at the recovered resume label. The entire actual final configuration equals the resumed parent frame: every other parent bank and ancestor prefix remains literal, the output extent becomes exactly |w|, every logical work head is parked at zero, and the stack suffix is restored. Writing E for parent visited extents, W=|w|, and n for fixed continuation-control size, the complete actual clock is at most span(E+1)+n+W+2max(W,Eout)+12. All addresses, lengths and depths occur only in proof frames, never delta. Recursive execution induction and fast multiplication remain separate targets.
-- source:
--   Original complete physical parent resumption for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveResume
import Theorems.Thm_IntMul_TrackedParentRestore_restore_correct
import Theorems.Thm_IntMul_TrackedParentOutputBridge_output_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveResume IntMul.FlatRecursiveScheduler IntMul.FlatRecursiveCall IntMul.TrackedBankCleanup

theorem IntMul.FlatRecursiveResume.resume_parent_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (label : Fin n) (w : List Bool)
    (unique : ∀ j p, c.cells j p=M.startSym ↔ p=0)
    (tail : ∀ j p, extent j < p → c.cells j p=M.blank) :
    ∃ t, t ≤ span M (fun j => extent j+1)+n+w.length+2*max w.length (extent M.outTape)+12 ∧
      (machine M n request resume).step^[t]
        (childInspection M n request resume base rho sigma offset extent c label w)=
        resumedFrame M n request resume base rho sigma offset extent c label w := by sorry
