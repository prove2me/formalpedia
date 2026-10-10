-- Prove2me | Theorems.Thm_IntMul_FlatRecursiveScheduler_bootstrap_correct
-- name    : IntMul.FlatRecursiveScheduler.bootstrap_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T01:51:34.150705+00:00
-- url     : https://prove2.me/theorems/c25f0910-6112-46dc-b12f-572cf8909663
-- title:
--   Actual native initialization of a fixed-tape recursive scheduler in linear time
-- statement:
--   For every body M and finite request/resume table, the one fixed recursive scheduler reaches its complete body-start frame from its ordinary native input x#y within 5L+12 actual transitions, where L is the input-word length. The reached state is the same body qStart used at all recursion depths, every work bank is the exact tracked embedding of M.initCfg, all work heads are at offset one, the shared buffer is physically empty with its local marker and head just after the empty word, the continuation tape is physically fresh with its head at one, and the original input is retained. The conclusion is equality of the entire configuration. Copying, work-bank preparation, stack-head normalization, buffer rewind and all dispatches are charged. This is actual startup correctness; it does not claim recursive execution or a fast multiplication bound.
-- source:
--   Original depth-independent scheduler startup for integer-multiplication shared foundations. Written by Codex.

import Definitions.Def_IntMul_FlatRecursiveScheduler
import Theorems.Thm_IntMul_TrackedRootInputCopy_copy_correct
import Theorems.Thm_IntMul_TrackedBankPreparation_setup_correct
import Theorems.Thm_IntMul_FixedTapeExtension_simulate_run
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic

open IntMul IntMul.FlatRecursiveScheduler IntMul.TrackedBankPreparation

theorem IntMul.FlatRecursiveScheduler.bootstrap_correct (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K) (x y : List Bool) :
    ∃ t, t ≤ 5*(inputWord M x y).length+12 ∧
      (machine M n request resume).step^[t] ((machine M n request resume).initCfg x y)=
        bodyFrame M n request resume (nativeBase M n request resume x y) 1 1 (fun _ => 1)
          (initialExtent M x y) (M.initCfg x y) [] := by sorry
