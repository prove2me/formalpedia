-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_initial_weight_le
-- name    : JohnsonApprox.MaxSatWeighted.initial_weight_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:14:36.809358+00:00
-- url     : https://prove2.me/theorems/1b9391a9-bcec-48e9-a4a6-9efabf7a94aa
-- title:
--   Proof of Theorem 3 — the initial weight of LEFT is at most |S|/2^k
-- statement:
--   Let $S$ be a finite set of clauses each containing at least $k$ distinct literals, and let B2 start on $S$, so that every clause $C$ has weight $w(C) = 2^{-|C|}$ and $\mathrm{LEFT} = S$. Then
--   $$\sum_{C \in \mathrm{LEFT}} w(C) \;\le\; \frac{|S|}{2^k}.$$
--
--   This is the starting point of the weight argument behind Theorem 3.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), p. 263, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (p. 263): initially, the total weight of the clauses in `LEFT` is at most
`|S|/2^k` when every clause of `S` has at least `k` literals. -/
theorem initial_weight_le (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (init S).weight (init S).LEFT ≤ (S.card : ℚ) / 2 ^ k := by sorry

end JohnsonApprox.MaxSatWeighted
