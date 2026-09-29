-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_halt_dead_weight_one
-- name    : JohnsonApprox.MaxSatWeighted.halt_dead_weight_one
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:25:28.294311+00:00
-- url     : https://prove2.me/theorems/44c40fb2-6f95-4dcd-90c3-8c2f045c849b
-- title:
--   Proof of Theorem 3 — every dead clause has final weight 1
-- statement:
--   Let $S$ be any finite set of clauses and consider a state of algorithm B2 reached from its start on $S$ in which Step 2 halts, i.e. no literal of any clause of LEFT is still in LIT. Then every clause $C$ remaining in LEFT has weight
--   $$w(C) = 1.$$
--
--   Each such clause has had all of its literals removed from LIT without being made true ("wounded as many times as it had literals"), and each wound doubled its weight, starting from $2^{-|C|}$. Together with the weight bound on LEFT this gives $|\mathrm{LEFT}| \le |S|/2^k$.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 264, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264): when B2 halts, every (dead) clause remaining in `LEFT` has
weight exactly `1`. -/
theorem halt_dead_weight_one (S : Finset Shared.Clause) (σ : State) (hσ : Reachable S σ)
    (hhalt : Halts σ) : ∀ C ∈ σ.LEFT, σ.w C = 1 := by sorry

end JohnsonApprox.MaxSatWeighted
