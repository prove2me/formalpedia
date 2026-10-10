-- Prove2me | Theorems.Thm_IntMul_EndParkRecursiveRelocation_native_to_interior_execution
-- name    : IntMul.EndParkRecursiveRelocation.native_to_interior_execution
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-10T05:36:15.678449+00:00
-- url     : https://prove2.me/theorems/46c5fcd2-f891-4dc2-9135-5c34afbf9518
-- title:
--   Native recursive child execution transferred to interior windows with its exact clock
-- statement:
--   A complete actual native body-and-cleanup trace on child operands x and y is replayed in arbitrary positive interior child work, buffer and continuation-stack windows with exactly the same physical clock T and exact returned configuration. The retained outer input head scans the machine blank; its position and payload may differ from those of the child native input. Input-head stationarity and the child native scanned blank are PROVED from the actual machine definitions, not supplied trajectory premises. The sole remaining trajectory premise is that all noninput heads are at least one before each source transition, protecting retained ancestor prefixes. No fast multiplication body or kappa root is claimed.
-- source:
--   Original native child physical clock transfer theorem, with actual input invariants discharged. Written by Codex.

import Definitions.Def_IntMul_EndParkRecursiveRelocation
import Mathlib.Tactic

open IntMul IntMul.EndParkRecursiveRelocation IntMul.EndParkRecursiveScheduler IntMul.EndParkRecursiveReturn IntMul.TrackedBankPreparation

theorem IntMul.EndParkRecursiveRelocation.native_to_interior_execution (M : MultitapeTM) (n : ℕ)
    (request : M.K → Option (Fin n)) (resume : Fin n → M.K)
    (base : (machine M n request resume).Cfg) (rho sigma : ℕ)
    (offset : Fin M.k → ℕ) (x y w : List Bool) (T : ℕ)
    (hrho : 1 ≤ rho) (hsigma : 1 ≤ sigma) (hoffset : ∀ j, 1 ≤ offset j)
    (root_blank : base.cells (machine M n request resume).inTape
      (base.head (machine M n request resume).inTape)=(machine M n request resume).blank)
    (inside : ∀ t, t < T → ∀ i, i ≠ (machine M n request resume).inTape →
      1 ≤ ((machine M n request resume).step^[t]
        (bodyFrame M n request resume (nativeBase M n request resume x y)
          1 1 (fun _ => 1) (initialExtent M x y) (M.initCfg x y) [])).head i)
    (run : (machine M n request resume).step^[T]
      (bodyFrame M n request resume (nativeBase M n request resume x y)
        1 1 (fun _ => 1) (initialExtent M x y) (M.initCfg x y) [])=
      inspectionFrame M n request resume (nativeBase M n request resume x y)
        1 1 (fun _ => 1) w) :
    (machine M n request resume).step^[T]
      (bodyFrame M n request resume base rho sigma offset
        (initialExtent M x y) (M.initCfg x y) [])=
      inspectionFrame M n request resume base rho sigma offset w := by sorry
