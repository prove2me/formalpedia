-- Prove2me | Theorems.Thm_MDPComplexity_PartiallyObserved_cost_splits_over_clause
-- name    : MDPComplexity.PartiallyObserved.cost_splits_over_clause
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:29.272428+00:00
-- url     : https://prove2.me/theorems/bfb0d796-51ec-49a3-b705-decaee66e037
-- title:
--   §4, proof of Theorem 6 (p. 449) — the cost splits over the clause chosen at time 1
-- statement:
--   Let $\varphi$ be a QSAT formula of the paper's alternating, three-literal form with $n$ variables and $m \ge 1$ clauses, let $M_\varphi$ be the partially observed process built from it in the proof of Theorem 6, with horizon $T = 2n+2$, and let $\pi$ be any observation-history policy. For each clause $i$ let
--   $$
--   E_i(\pi) = \sum_{x:\ x_1 = A'_{i1}} P_\pi(x)\, \mathrm{cost}_\pi(x)
--   $$
--   be the part of the expected cost carried by the trajectories that move to $A'_{i1}$ at time $1$ (the process "chooses" clause $C_i$). Then
--
--   1. the probability of choosing clause $i$ is $\sum_{x:\ x_1 = A'_{i1}} P_\pi(x) = 1/m$;
--   2. $J_\pi(T) = \sum_{i=1}^m E_i(\pi)$;
--   3. $J_\pi(T) = 0$ if and only if $E_i(\pi) = 0$ for every clause $i$.
--
--   In the paper's words, a policy of zero expected cost "has zero expected cost for all such initial choices" of the clause; this is the first step of the "only if" direction of the reduction.
--
--   **Formalization Note.** $E_i(\pi)$ is the partial expectation; the conditional expected cost given the choice of clause $i$ is $m\,E_i(\pi)$ by item 1. Clause $i$ is Lean index $i-1$, and $A'_{i1}$ is `lvlA' i 0` (which is $A'_{i,n+1}$ when $n = 0$). The horizon is $2n+2$, corrected from the printed $2m+2$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 449, proof of Theorem 6

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

namespace MDPComplexity.PartiallyObserved

/-- §4, proof of Theorem 6 (p. 449): the transition from `s₀` "chooses" clause `C_i` by moving to
`A′_{i1}` with probability `1/m`; the expected cost is the sum over clauses of the partial
expectations over trajectories through `A′_{i1}` at time 1, each nonnegative, so it is zero iff
the cost is zero for every choice of clause. -/
theorem cost_splits_over_clause {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy) :
    (∀ i : Fin m,
      ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x = 1 / (m : ℝ)) ∧
    (φ.toPOMDP hm).expCost .s0 π (horizon n) =
      ∑ i : Fin m, ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x * (φ.toPOMDP hm).trajCost π (horizon n) x ∧
    ((φ.toPOMDP hm).expCost .s0 π (horizon n) = 0 ↔
      ∀ i : Fin m, ∑ x ∈ Finset.univ.filter (fun x : Fin (horizon n + 1) → St n m =>
          x ⟨1, by unfold horizon; omega⟩ = lvlA' i 0),
        (φ.toPOMDP hm).trajProb .s0 π (horizon n) x * (φ.toPOMDP hm).trajCost π (horizon n) x = 0) := by sorry

end MDPComplexity.PartiallyObserved
