-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatGreedy_halt_sub_ge_k_left
-- name    : JohnsonApprox.MaxSatGreedy.halt_sub_ge_k_left
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:23:09.892342+00:00
-- url     : https://prove2.me/theorems/ada82e94-4c02-44d9-b56c-fcefd9cd6ade
-- title:
--   Proof of Theorem 2: at halting |SUB| ≥ k·|LEFT|, and SUB, LEFT partition S
-- statement:
--   Let $k \ge 0$ and let $S$ be an input of $MS(k)$: every clause of $S$ has at least $k$ distinct literals. Let $\sigma$ be a state reached by algorithm B1 from the initial state on $S$ at which Step 2 halts. Then
--   $$k \cdot |\mathrm{LEFT}_\sigma| \;\le\; |\mathrm{SUB}_\sigma|,$$
--   and SUB and LEFT are disjoint with $\mathrm{SUB}_\sigma \cup \mathrm{LEFT}_\sigma = S$.
--
--   Consequently B1 always returns at least $\tfrac{k}{k+1}|S|$ clauses, which is stronger than the ratio bound of Theorem 2 since $S^* \le |S|$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 262, proof of Theorem 2

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatGreedy_B1

namespace JohnsonApprox.MaxSatGreedy

theorem halt_sub_ge_k_left (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hh : Halts σ) :
    k * σ.LEFT.card ≤ σ.SUB.card ∧ Disjoint σ.SUB σ.LEFT ∧ σ.SUB ∪ σ.LEFT = S := by sorry

end JohnsonApprox.MaxSatGreedy
