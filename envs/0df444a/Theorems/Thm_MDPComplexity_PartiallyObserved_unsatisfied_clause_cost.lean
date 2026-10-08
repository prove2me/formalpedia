-- Prove2me | Theorems.Thm_MDPComplexity_PartiallyObserved_unsatisfied_clause_cost
-- name    : MDPComplexity.PartiallyObserved.unsatisfied_clause_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T06:02:40.284264+00:00
-- url     : https://prove2.me/theorems/dd180dce-753d-444b-b6d3-e286ae6887cb
-- title:
--   §4, proof of Theorem 6 (p. 449) — ending in $A'_{i,n+1}$ with positive probability costs at least $2^{-n}/m$
-- statement:
--   Let $\varphi$ be a QSAT formula of the paper's alternating, three-literal form with $n$ variables and $m \ge 1$ clauses, $M_\varphi$ the partially observed process of the proof of Theorem 6 with horizon $T = 2n+2$, and $\pi$ an observation-history policy. If some trajectory $x_0, \dots, x_T$ has positive probability under $\pi$ and is at the state $A'_{i,n+1}$ (clause $C_i$ unsatisfied at the end) at time $2n+1$, then
--   $$
--   J_\pi(T) \ \ge\ \frac{2^{-n}}{m}.
--   $$
--
--   The constant comes from the probability of a single trajectory: $1/m$ for the choice of the clause at time $1$ and $1/2$ for each universal variable, of which there are at most $n$. This is the step of the paper's argument showing that a zero-cost policy must lead the process to $A_{i,n+1}$ for every clause and every outcome of the universal variables.
--
--   **Formalization Note.** The paper says "for some choices of decisions for the universal variables the process ends up in $A'_{i,n+1}$"; we state it for any trajectory of positive probability ending there at time $2n+1$ (the only time at which the process can be there). $A'_{i,n+1}$ is `Aend' i`, clause $i$ is Lean index $i-1$. The horizon is $2n+2$, corrected from the printed $2m+2$.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 449, proof of Theorem 6

import Mathlib
import Definitions.Def_MDPComplexity_PartiallyObserved_Construction

namespace MDPComplexity.PartiallyObserved

/-- §4, proof of Theorem 6 (p. 449): if, under policy `π`, some trajectory of positive probability
is at `A′_{i,n+1}` at time `2n + 1`, then the expected cost is at least `2^{−n}/m`. -/
theorem unsatisfied_clause_cost {n m : ℕ} (φ : QBF n m) (hm : 0 < m)
    (hqsat : φ.IsPaperQSAT)
    (π : (φ.toPOMDP hm).Policy) (i : Fin m) (x : Fin (horizon n + 1) → St n m)
    (hx : 0 < (φ.toPOMDP hm).trajProb .s0 π (horizon n) x)
    (hend : x ⟨2 * n + 1, by unfold horizon; omega⟩ = .Aend' i) :
    (2 : ℝ)⁻¹ ^ n / m ≤ (φ.toPOMDP hm).expCost .s0 π (horizon n) := by sorry

end MDPComplexity.PartiallyObserved
