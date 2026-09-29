-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_shapley_unique_symmetric_marginal
-- name    : MonotonicSolutions.StrongMono.shapley_unique_symmetric_marginal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T20:12:01.839571+00:00
-- url     : https://prove2.me/theorems/9eca5113-87cd-48c7-932f-4bbdd91a82bc
-- title:
--   Theorem 2 with (7) in place of strong monotonicity
-- statement:
--   Let $N = \{1, \dots, n\}$ and let $\varphi$ assign to each game $v$ on $N$ (with $v(\emptyset) = 0$) a vector $\varphi(v) \in \mathbb{R}^N$. Then $\varphi$ is an allocation procedure, symmetric, and satisfies the marginality condition
--   $$v^i(S) = w^i(S) \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) = \varphi_i(w) \tag{7}$$
--   if and only if $\varphi(v)$ is the Shapley value of $v$ for every game $v$.
--
--   Young remarks after the proof of Theorem 2 that the argument only uses (7), a condition weaker than strong monotonicity; this is the resulting characterization, in which the three axioms are efficiency, symmetry and independence of each player's payoff from everything except his own marginal contributions.
--
--   **Formalization Note** Same conventions as the goal theorem (players `Fin n`, `Game n` with $v(\emptyset) = 0$, published `ShapleyValue`, standard reading of the permuted game).
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 71 ("The above proof only requires the assumption … (7)")

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_ShapleyValue
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71): the proof of Theorem 2 only uses (7). For a map `φ` from games on
`N = Fin n` to allocations, `φ` is an (efficient) allocation procedure, symmetric and
satisfies (7) if and only if `φ(v)` is the Shapley value of `v` for every game `v`. -/
theorem shapley_unique_symmetric_marginal {n : ℕ} (φ : Game n → Fin n → ℝ) :
    (IsAllocationProcedure φ ∧ IsSymmetric φ ∧ IsMarginal φ) ↔
      ∀ v : Game n, φ v = Supermodularity.Cooperative.ShapleyValue v.1 := by sorry

end MonotonicSolutions.StrongMono
