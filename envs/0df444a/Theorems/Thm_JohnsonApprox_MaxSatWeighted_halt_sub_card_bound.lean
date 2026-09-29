-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_halt_sub_card_bound
-- name    : JohnsonApprox.MaxSatWeighted.halt_sub_card_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:29:59.96399+00:00
-- url     : https://prove2.me/theorems/59b638af-52d4-40f5-9f6b-3266530863fe
-- title:
--   Proof of Theorem 3 — at halting, |LEFT| ≤ |S|/2^k and |SUB| ≥ |S|(1 − 1/2^k)
-- statement:
--   Let $S$ be a finite set of clauses each containing at least $k$ distinct literals, and consider a state of algorithm B2 reached from its start on $S$ in which the algorithm halts. Then
--   $$|\mathrm{LEFT}| \le \frac{|S|}{2^k} \qquad\text{and}\qquad |\mathrm{SUB}| \ge |S|\Bigl(1 - \frac{1}{2^k}\Bigr).$$
--
--   The second bound does not involve $S^*$: as the paper remarks, B2 always returns at least $\lceil |S|(2^k-1)/2^k\rceil$ clauses. Since $S^* \le |S|$, it gives the upper bound of Theorem 3.
--
--   **Formalization Note** Both bounds are multiplied out in $\mathbb N$: $2^k\,|\mathrm{LEFT}| \le |S|$ and $(2^k - 1)\,|S| \le 2^k\,|\mathrm{SUB}|$ (for $k \ge 0$, $2^k - 1 \ge 0$ so the truncated subtraction is exact).
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 264, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 264): when B2 halts on an input `S` of `MS(k)`,
`|LEFT| ≤ |S|/2^k` and `|SUB| ≥ |S|(1 − 1/2^k)`, stated without division. -/
theorem halt_sub_card_bound (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) (σ : State)
    (hσ : Reachable S σ) (hhalt : Halts σ) :
    2 ^ k * σ.LEFT.card ≤ S.card ∧ (2 ^ k - 1) * S.card ≤ 2 ^ k * σ.SUB.card := by sorry

end JohnsonApprox.MaxSatWeighted
