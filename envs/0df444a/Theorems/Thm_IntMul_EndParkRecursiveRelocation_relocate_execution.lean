-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveRelocation_relocate_execution
-- name    : IntMul.EndParkRecursiveRelocation.relocate_execution
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:11:49.904327+00:00
-- url     : https://prove2.me/theorems/db0c25f8-dd23-46dd-ada1-5c6f62aa7698
-- title:
--   Same-clock interior execution of a complete recursive body and cleanup trace
-- statement:
--   A complete physical body-and-cleanup trace of the actual optimized recursive scheduler, from unit-offset body banks to the exact cleaned root inspection frame, is replayed in arbitrary positive interior work, shared-buffer and stack windows with EXACTLY the same number T of transitions. The resulting whole configuration is the exact interior child return/inspection frame, preserving every ancestor prefix and the outer input tape. The two outer input heads may have different positions and different payloads, but must scan the same symbol. Input actions are stationary along the source trace, and each noninput source head is at least one before every transition. These explicit protected-window conditions remain premises. No new machine, address oracle, depth-dependent control or multiplied child clock is introduced.
-- source:
--   Original exact native-to-interior physical recursive trace framing theorem. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveRelocation IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn

theorem IntMul.EndParkRecursiveRelocation.relocate_execution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base source : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset extent : Fin M.k → ℕ) (c : M.Cfg) (v w : List Bool) (T : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_reads : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=
      source.cells (machine M n request resume).inTape
        (source.head (machine M n request resume).inTape))
    (root_quiet : ∀ t, t < T →
      let d := (machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)
      (((machine M n request resume).δ d.state (fun i => d.cells i (d.head i))).2
        (machine M n request resume).inTape).2=Move.stay)
    (inside : ∀ t, t < T → ∀ i, i≠(machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)).head i)
    (run : (machine M n request resume).step^[T]
      (bodyFrame M n request resume source 1 1 (fun _ => 1) extent c v)=
      inspectionFrame M n request resume source 1 1 (fun _ => 1) w) :
    (machine M n request resume).step^[T]
      (bodyFrame M n request resume base rho sigma offset extent c v)=
      inspectionFrame M n request resume base rho sigma offset w := by sorry
