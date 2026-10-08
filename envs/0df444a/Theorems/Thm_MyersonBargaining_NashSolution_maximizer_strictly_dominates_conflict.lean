-- Prove2me | Theorems.Thm_MyersonBargaining_NashSolution_maximizer_strictly_dominates_conflict
-- name    : MyersonBargaining.NashSolution.maximizer_strictly_dominates_conflict
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:10.862909+00:00
-- url     : https://prove2.me/theorems/d213559c-7bc5-4085-8765-512e5e9cf69c
-- title:
--   Section 5 — every Nash-product maximizer strictly improves every conflict payoff
-- statement:
--   Let $t$ be the conflict payoff vector and suppose some $y\in F^*$ strictly dominates it in every player-type coordinate. If $x$ is a maximizer of the generalized Nash product over $F^*_+$, then
--
--   $$
--   x_{i,a_i}>t_{i,a_i}\qquad\text{for every player }i\text{ and type }a_i.
--   $$
--
--   Thus every bargaining solution lies strictly above the conflict point when that strict improvement is feasible. The maximum property here includes both membership in $F^*_+$ and comparison with every point of that set.
--
--   **Formalization Note** The paper's "$t$ is strictly dominated in $F^*$" is the hypothesis that some $y\in F^*$ has $y_{i,a_i}>t_{i,a_i}$ for all $i,a_i$. A "maximum point" is a vector of $F^*_+$ at which (18) is at least its value at every point of $F^*_+$; neither the existence of a maximum nor its positivity is assumed. The generalized Nash product uses real powers with exponents $R_i(a_i)>0$.
-- source:
--   Myerson, Incentive compatibility and the bargaining problem, Econometrica 47 (1979), p. 69, proof of Theorem 3

import Mathlib
import Definitions.Def_MyersonBargaining_NashSolution_Bargaining

namespace MyersonBargaining.NashSolution

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  {A : ι → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
  [∀ i, Nonempty (A i)] {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]

/-- Proof of Theorem 3, p. 69: every product maximizer improves all conflict payoffs. -/
theorem maximizer_strictly_dominates_conflict
    (G : Problem ι A C) (cstar : C)
    (h : ∃ y ∈ FStar G, StrictlyDominates y (conflictPayoff G cstar))
    (x : (Σ i, A i) → ℝ) (hx : IsBargainingSolution G cstar x) :
    StrictlyDominates x (conflictPayoff G cstar) := by sorry

end MyersonBargaining.NashSolution
