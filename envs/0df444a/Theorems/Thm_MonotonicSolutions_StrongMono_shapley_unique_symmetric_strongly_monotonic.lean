-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_shapley_unique_symmetric_strongly_monotonic
-- name    : MonotonicSolutions.StrongMono.shapley_unique_symmetric_strongly_monotonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:11:27.214947+00:00
-- url     : https://prove2.me/theorems/78460855-0b23-4775-8847-17a76f8d828a
-- title:
--   Theorem 2 — the Shapley value is the unique symmetric strongly monotonic allocation procedure
-- statement:
--   Let $N = \{1, \dots, n\}$. A cooperative game is a function $v$ on the coalitions $S \subseteq N$ with $v(\emptyset) = 0$, and $v^i(S)$ is the marginal contribution of player $i$ to $S$ (Eq. (3)). Let $\varphi$ be any map assigning to each game $v$ a vector $\varphi(v) \in \mathbb{R}^N$. Then the following are equivalent:
--
--   1. $\varphi$ is an allocation procedure ($\sum_{i \in N} \varphi_i(v) = v(N)$ for every $v$), $\varphi$ is symmetric ($\varphi_{\pi i}(\pi v) = \varphi_i(v)$ for every permutation $\pi$ of $N$, where $(\pi v)(\pi S) = v(S)$), and $\varphi$ is strongly monotonic ($v^i(S) \ge w^i(S)$ for all $S$ implies $\varphi_i(v) \ge \varphi_i(w)$);
--   2. $\varphi$ is the Shapley value: for every game $v$ and every player $i$,
--   $$\varphi_i(v) = \sum_{S \subseteq N,\ i \in S} \frac{(|S|-1)!\,(|N|-|S|)!}{|N|!}\, v^i(S).$$
--
--   This is Young's characterization of the Shapley value: efficiency, symmetry and strong monotonicity determine it, with no additivity axiom and no separate dummy axiom. The implication from 2 to 1 says the Shapley value has the three properties; the implication from 1 to 2 is the uniqueness.
--
--   **Formalization Note** Players are `Fin n`; games are `Game n = {v : Finset (Fin n) → ℝ // v ∅ = 0}` (the normalisation is required: without it a constant game would receive $c/n$ per player from any efficient symmetric procedure but $0$ from the Shapley formula). The Shapley value is the published `Supermodularity.Cooperative.ShapleyValue`, written over $S \setminus \{i\}$. Symmetry uses the standard reading $(\pi v)(\pi S) = v(S)$ of the paper's misprinted "$\pi v(S) = v(\pi S)$"; see the definition file. The player set is fixed; no lower bound on $n$ is needed.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, Theorem 2

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Theorem 2 of Young (1985, p. 70): the Shapley value is the unique symmetric allocation
procedure that is strongly monotonic. For a map `φ` from games on `N = Fin n` to allocations,
`φ` is an (efficient) allocation procedure, symmetric and strongly monotonic if and only if
`φ(v)` is the Shapley value of `v` for every game `v`. -/
theorem shapley_unique_symmetric_strongly_monotonic {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsStronglyMonotonic φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by sorry

end MonotonicSolutions.StrongMono
