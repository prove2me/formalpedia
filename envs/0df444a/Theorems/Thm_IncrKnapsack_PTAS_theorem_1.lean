-- Prove2me | Theorems.Thm_IncrKnapsack_PTAS_theorem_1
-- name    : IncrKnapsack.PTAS.theorem_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:21.649993+00:00
-- url     : https://prove2.me/theorems/4e683511-fd91-40a1-8195-c0fff35342e8
-- title:
--   Theorem 1, p. 4 (restated p. 19) — for every ε′ > 0 some accuracy 1/K makes the cluster DP's output feasible and (1 − ε′)-optimal
-- statement:
--   This is the approximation clause of the main theorem of Aouad and Segev: for any accuracy level $\epsilon' > 0$, the incremental knapsack problem can be approximated within factor $1 - \epsilon'$ of optimal, by the algorithm of Section 3.
--
--   Precisely: for every $\epsilon' > 0$ there is an integer $K > 4$ (so the algorithm runs with accuracy $\epsilon = 1/K < 1/4$) with the following property. Take any instance satisfying the standing assumptions and any optimal solution $\mathcal S^*$ for its original profits $p$. For every shift $\xi \in \{0,\dots,K-1\}$ the algorithm uses three ingredients: a profit grid $\Phi_\xi$, a single-cluster subroutine $\mathcal A_\xi$ with the guarantee of Theorem 3 (super-optimal weight, profit at least $(1-\epsilon)\phi$), and a traceback of its approximate program $\tilde F$ on the rounded profits. Let $\bar{\mathcal S}_\xi$ be the solution glued along that traceback. Then
--
--   1. every $\bar{\mathcal S}_\xi$ is feasible, and
--   2. some shift $\xi$ satisfies
--   $$\Psi_p(\bar{\mathcal S}_\xi) \ge (1-\epsilon')\cdot\Psi_p(\mathcal S^*).$$
--
--   The algorithm enumerates the shifts and returns the best $\bar{\mathcal S}_\xi$, which is therefore a feasible $(1-\epsilon')$-approximate solution. The accuracy $K$ depends on $\epsilon'$ only, not on the instance.
--
--   **Formalization Note.** The running-time half of Theorem 1, $O(n^{\tilde O(1/\epsilon^3)}\cdot|\mathcal I|^{O(1)})$, is not formalized: $\tilde O$ hides unquantified polylogarithmic factors and there is no machine model. The single-cluster subroutine of Theorem 3 (Section 2) enters only through its guarantee. That guarantee is a hypothesis met by the exact single-cluster optimum, so it is satisfiable. Everything else is constructed: rounding, clusters, $\tilde F$ and the glued solution. The traceback may choose any minimizer. Added standing assumptions: capacities are nonnegative and every item fits into $W_T$. The profit grid is the property (15) on $[0, \lambda^{1+}\sum_i p_i]$, replacing the printed grid (7), which is too short for Lemma 11.
-- source:
--   Aouad & Segev, An Approximate Dynamic Programming Approach to the Incremental Knapsack Problem, arXiv:2010.07633v1, p. 4 (restated p. 19), Theorem 1

import Mathlib
import Definitions.Def_IncrKnapsack_PTAS_Model

open Classical
open Finset BigOperators

namespace IncrKnapsack.PTAS

theorem theorem_1 :
    ∀ ε' : ℝ, 0 < ε' → ∃ K : ℕ, 4 < K ∧
      ∀ (I : Instance), I.Standing →
      ∀ Sstar : Sol I, IsOptimal I I.p Sstar →
      ∀ (Φ : ℕ → Finset ℝ) (A : ℕ → Subroutine I) (jt : ℕ → ℕ → ℕ) (ϕt : ℕ → ℕ → ℝ),
        (∀ ξ < K, IsProfitGrid I K ξ (Φ ξ) ∧ IsSubroutine I K ξ (A ξ) ∧
          IsTraceback I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ)) →
        (∀ ξ < K, Feasible I (algOut I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ))) ∧
        ∃ ξ < K, (1 - ε') * Psi I I.p Sstar ≤
          Psi I I.p (algOut I K ξ (Φ ξ) (A ξ) (jt ξ) (ϕt ξ)) := by sorry
end IncrKnapsack.PTAS
