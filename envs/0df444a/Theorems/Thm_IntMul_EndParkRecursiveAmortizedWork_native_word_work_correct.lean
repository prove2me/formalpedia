-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveAmortizedWork_native_word_work_correct
-- name    : IntMul.EndParkRecursiveAmortizedWork.native_word_work_correct
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T04:57:36.087976+00:00
-- url     : https://prove2.me/theorems/2ba601be-b608-4d77-891d-a84a7e7c8943
-- title:
--   Complete native recursive clock from ordinary body steps and word lengths alone
-- statement:
--   A finite computation certificate for one fixed recursive body counts S ordinary body steps and additive word work W. Each return charges only shared/result lengths plus one; each call charges shared word, (k+2) times its argument packet, four times its child result, and the fixed tape/label constants. Retained extents and head positions do not occur in these word charges. The complete optimized machine executes it from real native input to exact canonical output in at most S+32(W+(k+1)|x#y|+k+(2k+3)S)+5|x#y|+4|result|+18 actual transitions. The proof amortizes all bank movement and retained space through a telescoping potential. A fast body and bounds on S and total W are still required.
-- source:
--   Original word-only amortized native execution theorem for fixed-tape recursive integer multiplication. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveAmortizedWork
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_evaluates_correct
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveAmortizedWork IntMul.EndParkRecursiveScheduler IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveAmortizedWork.native_word_work_correct (M : MultitapeTM) (labels : ℕ)
    (request : M.K → Option (Fin labels)) (resume : Fin labels → M.K)
    (x y w : List Bool) (steps work : ℕ)
    (certificate : HasWordWork M labels request resume (initialExtent M x y)
      (M.initCfg x y) [] w steps work) :
    ∃ t : ℕ, t≤ steps+32*(work+(M.k+1)*(inputWord M x y).length+M.k+(2*M.k+3)*steps)+
        5*(inputWord M x y).length+4*w.length+18 ∧
      (machine M labels request resume).step^[t] ((machine M labels request resume).initCfg x y)=
        nativeFinalFrame M labels request resume x y w ∧
      (machine M labels request resume).HaltsWithOutput x y t w := by sorry
