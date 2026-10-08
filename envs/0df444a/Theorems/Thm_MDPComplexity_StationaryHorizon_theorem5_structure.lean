-- Prove2me | Theorems.Thm_MDPComplexity_StationaryHorizon_theorem5_structure
-- name    : MDPComplexity.StationaryHorizon.theorem5_structure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:23.855918+00:00
-- url     : https://prove2.me/theorems/0d979eb9-eddd-41ae-87a5-73babf8b414d
-- title:
--   Theorem 5 cost identity: a short prefix plus a repeated closed walk
-- statement:
--   Let $M$ be a finite stationary deterministic process with $n$ states, initial state $s_0$, and horizon $T>n^2$. For $l\le T$ and a state $u$, let $w_{l,u}$ be the minimum cost of an $l$-arc walk from $s_0$ that visits $u$. Let $r_{k,u}$ be the minimum cost of a closed $k$-arc walk at $u$. Then
--
--   $$J_T^*(s_0)=\min_{\substack{l\le T,\ l<n^3,\ u\in S,\\1\le k\le n,\ k\mid T-l}}\left(w_{l,u}+\frac{T-l}{k}r_{k,u}\right),$$
--
--   where a candidate is included only when both component walk sets are nonempty. This identity is the mathematical correctness claim behind the paper's parallel algorithm for Theorem 5.
--
--   **Formalization Note** The paper states that the finite-horizon stationary deterministic problem is in NC. This item formalizes its cost identity, not that complexity classification. The algorithm's “shortest cycle of length $k$” is represented as a cheapest closed $k$-arc walk, as computed by a min-plus matrix power. The structural milestone separately uses a simple cycle. The conditions $l\le T$ and $k\mid T-l$ make the natural-number quotient exact. No no-ties hypothesis is imposed. The optimum remains over all time-dependent policies, and $T$ is the number of decision arcs.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 447, §3 The finite horizon, stationary case, paragraph before Theorem 5, https://doi.org/10.1287/moor.12.3.441

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447, identity underlying Theorem 5: minimize over a short prefix through
`u` and a repeated closed `k`-walk at `u`. The minima in each component are genuine
walk minima, and the outer optimum remains over all time-dependent policies. -/
theorem theorem5_structure (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    IsLeast
      {x : ℝ | ∃ (l k : ℕ) (u : S) (w r : ℝ),
        l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
        1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
        IsLeast {y : ℝ | ∃ W : M.Walk l,
          W.x 0 = s₀ ∧ (∃ t : Fin (l + 1), W.x t = u) ∧ y = W.cost} w ∧
        IsLeast {y : ℝ | ∃ C : M.Walk k,
          C.x 0 = u ∧ C.x ⟨k, Nat.lt_succ_self k⟩ = u ∧ y = C.cost} r ∧
        x = w + (((T - l) / k : ℕ) : ℝ) * r}
      (M.optHorizon s₀ T) := by sorry

end MDPComplexity.StationaryHorizon
