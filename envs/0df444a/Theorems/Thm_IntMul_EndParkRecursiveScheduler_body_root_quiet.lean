-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveScheduler_body_root_quiet
-- name    : IntMul.EndParkRecursiveScheduler.body_root_quiet
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:32:54.605484+00:00
-- url     : https://prove2.me/theorems/0cd7e1ad-4f8f-4d0d-9200-de124e1367bf
-- title:
--   Stationary outer input throughout actual recursive scheduler execution after body entry
-- statement:
--   Starting from any body frame of the actual optimized recursive scheduler, every later actual transition has Move.stay on the outer input tape. This holds for every time, every base configuration, body state, result word and window position, without a supplied trajectory invariant. It includes recursive body execution, reservation, child input bridging, continuation push and pop, cleanup, return replacement and selective parent restoration, as well as final output processing.
-- source:
--   Original actual recursive machine input-head invariant. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveExecution
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveScheduler

theorem IntMul.EndParkRecursiveScheduler.body_root_quiet (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v : List Bool) (t : ℕ) :
    let d := (machine M n request resume).step^[t]
      (bodyFrame M n request resume base rho sigma offset extent c v)
    (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
      (machine M n request resume).inTape).2=Move.stay := by sorry
