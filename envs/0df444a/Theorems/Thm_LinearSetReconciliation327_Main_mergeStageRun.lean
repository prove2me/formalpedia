-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_mergeStageRun
-- name    : LinearSetReconciliation327.Main.mergeStageRun
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-22T04:11:39.633768+00:00
-- url     : https://prove2.me/theorems/aa63ddf0-38aa-4784-b766-f1f15f39845e
-- title:
--   The merge of Theorem 6.5's CR stage: a StageRun from dCrBase to dEnd whose output is x̂ △ ê
-- statement:
--   For every program `P`, environment `E`, output base `ob`, and every pair of word lists $A,B$ stored at `[ab, ab+al)` and `[bb, bb+bl)`, if the merge is located at `base` in `P`, the entry registers hold `(ab, al, bb, bl, ob)`, the lists are duplicate-free, every stored word is shorter than the word size, `ob` lies beyond both input blocks in the two-sided sense that each input block is either entirely below `ob` or entirely above `[ob, ob+al+bl)`, then the machine reaches `base + 86` in at most `mrgCost al bl` word operations, and in the reached state the output list is duplicate-free with value set exactly the symmetric difference $A \u25b3 B$.
-- source:
--   Theorem 6.5's CR stage of arXiv:2611.11409; `StageRun` from Definitions.Def_LinearSetReconciliation327_Main_Top65Dec; the merge program and its simulation from Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121.

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_MergeStep20261121

namespace LinearSetReconciliation327.Main

theorem mergeStageRun {P : Program} {E : RAMEnv} {base ab al bb bl ob : ℕ} (A B : List ℕ)
    (hAt : At P base (RMR.mrgStmtFull.compile base)) (hW : 1 < 2 ^ E.W) :
    StageRun P E base (base + RMR.mrgStmtFull.len) (RMR.mrgCost al bl)
      (fun s => s.regs r10 = ab ∧ s.regs r11 = al ∧ s.regs r12 = bb ∧ s.regs r13 = bl ∧
        s.regs r14 = ob ∧
        RMR.mList s.mem ab al = A ∧ RMR.mList s.mem bb bl = B ∧
        A.Nodup ∧ B.Nodup ∧
        (∀ p, p < al → s.mem (ab + p) < 2 ^ E.W) ∧
        (∀ p, p < bl → s.mem (bb + p) < 2 ^ E.W) ∧
        al < 2 ^ E.W ∧ bl < 2 ^ E.W ∧
        ab + al ≤ 2 ^ E.W ∧ bb + bl ≤ 2 ^ E.W ∧
        ob + (al + bl) + 1 < 2 ^ E.W ∧
        (ab + al ≤ ob ∨ ob + (al + bl) ≤ ab) ∧ (bb + bl ≤ ob ∨ ob + (al + bl) ≤ bb))
      (fun s' => (outList s').Nodup ∧
        (outList s').toFinset = symmDiff A.toFinset B.toFinset) := by sorry

end LinearSetReconciliation327.Main
