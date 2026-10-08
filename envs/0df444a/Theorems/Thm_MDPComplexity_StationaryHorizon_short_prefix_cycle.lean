-- Prove2me | Theorems.Thm_MDPComplexity_StationaryHorizon_short_prefix_cycle
-- name    : MDPComplexity.StationaryHorizon.short_prefix_cycle
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T05:45:20.667706+00:00
-- url     : https://prove2.me/theorems/f0a9c0d0-ef8c-4617-9892-6361a4958b5c
-- title:
--   Corrected short-prefix and repeated-simple-cycle structure
-- statement:
--   Let $M$ have $n$ states and let $T>n^2$. There are a cheapest $T$-arc walk $W$ from $s_0$, an $l$-arc walk $P$ from $s_0$ visiting a state $u$, and a simple cycle $C$ of $k$ arcs based at $u$, with $l\le T$, $l<n^3$, $1\le k\le n$, and $k\mid T-l$, such that
--
--   $$c(W)=c(P)+\frac{T-l}{k}\,c(C).$$
--
--   This is the cost form of the structure used in Theorem 5's algorithm.
--
--   **Formalization Note** The printed justification for the bound $l<n^3$ assumes that repetitions can be exchanged without breaking the walk's connectivity and that a no-ties perturbation settles all equal-length cycles. This statement retains the bound without a no-ties assumption. The condition $l\le T$ makes natural-number subtraction exact. A cycle may be a loop.
-- source:
--   Papadimitriou and Tsitsiklis, The Complexity of Markov Decision Processes, Math. Oper. Res. 12(3) (1987), p. 447, §3 The finite horizon, stationary case, structure paragraph (corrected), https://doi.org/10.1287/moor.12.3.441

import Mathlib
import Definitions.Def_MDPComplexity_StationaryHorizon_Model

namespace MDPComplexity.StationaryHorizon

variable {S : Type} [Fintype S]

/-- §3, p. 447: corrected numerical form of the short-prefix/one-cycle structure.
The prefix visits the cycle base, so copies of that cycle can be inserted there. -/
theorem short_prefix_cycle (M : DetMDP S) (s₀ : S) (T : ℕ)
    (hT : (Fintype.card S) ^ 2 < T) :
    ∃ (W : M.Walk T) (l k : ℕ) (u : S) (P : M.Walk l) (C : M.Walk k),
      W.x 0 = s₀ ∧
      IsLeast {y : ℝ | ∃ V : M.Walk T, V.x 0 = s₀ ∧ y = V.cost} W.cost ∧
      l ≤ T ∧ l < (Fintype.card S) ^ 3 ∧
      1 ≤ k ∧ k ≤ Fintype.card S ∧ k ∣ T - l ∧
      P.x 0 = s₀ ∧ (∃ t : Fin (l + 1), P.x t = u) ∧
      C.IsSimpleCycle ∧ C.x 0 = u ∧
      W.cost = P.cost + (((T - l) / k : ℕ) : ℝ) * C.cost := by sorry

end MDPComplexity.StationaryHorizon
