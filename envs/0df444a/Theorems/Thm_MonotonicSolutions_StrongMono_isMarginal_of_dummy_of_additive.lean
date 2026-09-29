-- Prove2me | Theorems.Thm_MonotonicSolutions_StrongMono_isMarginal_of_dummy_of_additive
-- name    : MonotonicSolutions.StrongMono.isMarginal_of_dummy_of_additive
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T20:12:46.516518+00:00
-- url     : https://prove2.me/theorems/964663ea-44dd-4a05-8927-d3109e1303f0
-- title:
--   Eq. (11) — Shapley's dummy axiom plus additivity implies (7)
-- statement:
--   Let $\varphi$ assign to each game $v$ on $N = \{1, \dots, n\}$ (with $v(\emptyset) = 0$) a vector $\varphi(v) \in \mathbb{R}^N$. Suppose $\varphi$ satisfies Shapley's **dummy axiom**
--   $$v^i(S) = 0 \text{ for all } S \subseteq N \quad \Longrightarrow \quad \varphi_i(v) = 0 \tag{11}$$
--   and Shapley's **additivity axiom** $\varphi(v + w) = \varphi(v) + \varphi(w)$ for all games $v, w$. Then $\varphi$ satisfies (7): for all games $v, w$ and every player $i$, $v^i(S) = w^i(S)$ for all $S$ implies $\varphi_i(v) = \varphi_i(w)$.
--
--   This places Theorem 2 relative to Shapley's original axioms: (7) is implied by dummy plus additivity, so the characterization with (7) contains Shapley's.
--
--   **Formalization Note** Neither efficiency nor symmetry is assumed. The sum of games is `addGame v w`, with values $v(S) + w(S)$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 71, Eq. (11) and the sentence after it

import Mathlib
import Definitions.Def_MonotonicSolutions_StrongMono_Game
import Definitions.Def_MonotonicSolutions_StrongMono_Axioms

namespace MonotonicSolutions.StrongMono

/-- Young (1985, p. 71): Shapley's dummy axiom (11) combined with his additivity axiom
implies (7): if `φ` satisfies `v^i(S) = 0` for all `S` ⇒ `φ_i(v) = 0`, and
`φ(v + w) = φ(v) + φ(w)` for all games, then `v^i(S) = w^i(S)` for all `S` implies
`φ_i(v) = φ_i(w)`. -/
theorem isMarginal_of_dummy_of_additive {n : ℕ} (φ : Game n → Fin n → ℝ)
    (hD : SatisfiesDummy φ) (hAdd : IsAdditive φ) : IsMarginal φ := by sorry

end MonotonicSolutions.StrongMono
