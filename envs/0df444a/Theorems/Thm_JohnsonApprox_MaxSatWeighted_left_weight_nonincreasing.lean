-- Prove2me | Theorems.Thm_JohnsonApprox_MaxSatWeighted_left_weight_nonincreasing
-- name    : JohnsonApprox.MaxSatWeighted.left_weight_nonincreasing
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T23:16:24.553038+00:00
-- url     : https://prove2.me/theorems/154f74a8-5557-4ed2-96de-96b7eaab8ff9
-- title:
--   Proof of Theorem 3 — the total weight of LEFT never increases
-- statement:
--   Let $S$ be a finite set of clauses each containing at least $k$ distinct literals, and consider any run of algorithm B2 on $S$ (with any admissible choices of the literal $y$ in Step 3).
--
--   1. In every iteration $\sigma \to \sigma'$ of the run, the total weight of the clauses in LEFT does not increase:
--   $$\sum_{C \in \mathrm{LEFT}'} w'(C) \;\le\; \sum_{C \in \mathrm{LEFT}} w(C).$$
--   2. Consequently, in every state reached by the run, and in particular when the algorithm halts,
--   $$\sum_{C \in \mathrm{LEFT}} w(C) \;\le\; \frac{|S|}{2^k}.$$
--
--   The reason, in the paper's words, is that the weight removed from LEFT in Step 4 is at least the weight added to the remaining clauses that are wounded.
--
--   **Formalization Note** Part 1 is stated for states reachable from the initial state (the paper's "during each iteration"); it uses that weights stay nonnegative, which holds along runs but not for arbitrary states.
-- source:
--   Johnson, Approximation algorithms for combinatorial problems, J. Comput. System Sci. 9 (1974), pp. 263–264, proof of Theorem 3

import Mathlib
import Definitions.Def_JohnsonApprox_Shared_Problem
import Definitions.Def_JohnsonApprox_MaxSatWeighted_B2

namespace JohnsonApprox.MaxSatWeighted

/-- Proof of Theorem 3 (pp. 263–264): along any run of B2 on an input of `MS(k)`, one iteration
never increases the total weight of `LEFT`, and so the weight of `LEFT` in every reachable
state (in particular at halting) is at most `|S|/2^k`. -/
theorem left_weight_nonincreasing (k : ℕ) (S : Finset Shared.Clause) (hS : Shared.InMS k S) :
    (∀ σ σ' : State, Reachable S σ → Step σ σ' → σ'.weight σ'.LEFT ≤ σ.weight σ.LEFT) ∧
    (∀ σ : State, Reachable S σ → σ.weight σ.LEFT ≤ (S.card : ℚ) / 2 ^ k) := by sorry

end JohnsonApprox.MaxSatWeighted
