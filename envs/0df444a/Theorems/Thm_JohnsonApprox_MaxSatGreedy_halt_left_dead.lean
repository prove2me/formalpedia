-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatGreedy_halt_left_dead
-- name    : JohnsonApprox.MaxSatGreedy.halt_left_dead
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:22:48.554034+00:00
-- url     : https://prove2.me/theorems/cf32841e-69b7-49a4-a218-651358665b59
-- title:
--   Proof of Theorem 2: when B1 halts, every clause left in LEFT is dead
-- statement:
--   Run algorithm B1 on a set $S$ of clauses and let $\sigma$ be a state reached from the initial state at which Step 2 halts. Then for every clause $C$ remaining in $\mathrm{LEFT}_\sigma$ and every literal $\ell \in C$,
--   $$\ell \notin \mathrm{TRUE}_\sigma \quad\text{and}\quad \bar\ell \in \mathrm{TRUE}_\sigma .$$
--   In other words, every literal of $C$ was removed from LIT when its complement was made true: $C$ has been wounded once for each of its literals and can no longer be satisfied by extending TRUE.
--
--   Together with the per-step accounting, this bounds the number of clauses B1 fails to satisfy.
--
--   **Formalization Note** "Reached from the initial state" is `Reachable S σ`; the conclusion is stated for every literal of every clause of LEFT, which is the paper's "wounded as many times as they contain literals".
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, proof of Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem halt_left_dead (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ) (hh : Halts σ) :
    ∀ C ∈ σ.LEFT, ∀ l ∈ C, l ∉ σ.TRUE ∧ l.neg ∈ σ.TRUE := by sorry

end JohnsonApprox.MaxSatGreedy
