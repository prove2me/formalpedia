-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_to_interior_clock
-- name    : IntMul.EndParkRecursiveEvaluation.native_to_interior_clock
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T07:55:21.534089+00:00
-- url     : https://prove2.me/theorems/b7a42203-bdf7-49a2-823a-d6e6abfbde1d
-- title:
--   Actual native child halt clock reused in interior windows with coefficient one
-- statement:
--   Suppose a finite actual recursive evaluation of child operands x,y returns word w, and the same physical recursive scheduler halts natively on x,y at clock H. For any positive interior work, buffer and continuation windows whose retained read-only input scans blank, the exact child body-and-cleanup execution reaches the complete inspection frame at a physical clock q no greater than the finite evaluation budget and strictly below H. No noninput trajectory hypothesis is supplied: complete recursive safety is proved. The native child clock has coefficient one, independent of loose logical evaluation budgets. All retained ancestor prefixes and the complete returned frame are preserved.
-- source:
--   Original coefficient-one actual native child clock integration for integer multiplication recursive foundations. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_evaluates_protected_prefix
import Theorems.Thm_IntMul_EndParkRecursiveEvaluation_native_prefix_clock
import Theorems.Thm_IntMul_EndParkRecursiveRelocation_native_to_interior_execution
import Mathlib.Data.List.GetD
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn IntMul.EndParkRecursiveEvaluation IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveEvaluation.native_to_interior_clock (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (x y w : List Bool) (budget H : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_blank : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=(machine M n request resume).blank)
    (evaluation : Evaluates M n request resume (initialExtent M x y)
      (M.initCfg x y) [] w budget)
    (halt : ((machine M n request resume).step^[H]
      ((machine M n request resume).initCfg x y)).state=(machine M n request resume).qHalt) :
    ∃ q, q ≤ budget ∧ q < H ∧
      (machine M n request resume).step^[q]
        (bodyFrame M n request resume base rho sigma offset
          (initialExtent M x y) (M.initCfg x y) [])=
        inspectionFrame M n request resume base rho sigma offset w := by sorry
