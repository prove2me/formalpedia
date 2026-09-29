-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_isMarginal_of_isStronglyMonotonic
-- name    : MonotonicSolutions.StrongMono.isMarginal_of_isStronglyMonotonic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:05:47.49798+00:00
-- url     : https://prove2.me/theorems/76b71183-c3d8-45bf-a26e-de20de96de7d
-- title:
--   Eq. (7) — strong monotonicity implies marginality
-- statement:
--   Let $\varphi$ assign to every game on $N = \{1, \dots, n\}$ a vector in $\mathbb{R}^N$, and suppose $\varphi$ is strongly monotonic, Eq. (6). Then for all games $v, w$ and every player $i$,
--   $$v^i(S) = w^i(S) \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) = \varphi_i(w). \tag{7}$$
--
--   In words: a strongly monotonic procedure pays each player an amount that depends only on the vector of that player's marginal contributions. This is the first step of the uniqueness part of Theorem 2.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 70, Eq. (7)

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Eq. (7) of Young (1985, p. 70): a strongly monotonic map `φ` depends, for each player,
only on that player's marginal contributions: `v^i(S) = w^i(S)` for all `S` implies
`φ_i(v) = φ_i(w)`. -/
theorem isMarginal_of_isStronglyMonotonic {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hφ : IsStronglyMonotonic φ) : IsMarginal φ := by sorry

end MonotonicSolutions.StrongMono
