-- Prove2me | Theorems.Thm_IntMul_FiniteCaller_simulate_run
-- name    : IntMul.FiniteCaller.simulate_run
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-09T19:44:24.773663+00:00
-- url     : https://prove2.me/theorems/95078419-c486-4666-b47e-0ed9b928d63b
-- title:
--   Literal finite-state compiler: exact live segments and charged subroutine returns
-- statement:
--   For any campaign multitape machine M, finite caller-state type E, initial caller state, finite dispatch function, current caller state e, arbitrary subroutine configuration c, and time T, the compiled single machine preserves the complete run interface. If M's T-step configuration is nonterminal, the compiled machine simulates exactly T actual transitions and reaches its exact embedding. If it is terminal, the compiled machine reaches the exact dispatched complete final configuration in at most T+1 actual transitions. Dispatch sees only finite caller state and scanned symbols and can resume at another subroutine state, change caller state, or enter global halt. It preserves every physical tape and head position. The terminal proof refines a possibly padded frozen trace to its first halt before transferring control. This supplies a literal finite-table composition interface, not the recursive multiplication scheduler.
-- source:
--   The campaign MultitapeTM conventions and exact machine model, published definition 47ff1689-4e87-4af2-9406-674787e32429. Original finite-table compiler and interface formalization, Written by Codex.

import Definitions.Def_IntMul_FiniteCaller
import Mathlib.Tactic

open IntMul.FiniteCaller

theorem IntMul.FiniteCaller.simulate_run (M : IntMul.MultitapeTM) (E : Type) [Fintype E] (initial e : E)
    (dispatch : E → (Fin M.k → M.Sym) → Option (E × M.K)) (c : M.Cfg) (T : ℕ) :
    ((M.step^[T] c).state ≠ M.qHalt →
      (machine M E initial dispatch).step^[T] (embed M E initial e dispatch c) =
        embed M E initial e dispatch (M.step^[T] c)) ∧
    ((M.step^[T] c).state = M.qHalt →
      ∃ t : ℕ, t ≤ T + 1 ∧
        (machine M E initial dispatch).step^[t] (embed M E initial e dispatch c) =
          returned M E initial e dispatch (M.step^[T] c)) := by sorry
