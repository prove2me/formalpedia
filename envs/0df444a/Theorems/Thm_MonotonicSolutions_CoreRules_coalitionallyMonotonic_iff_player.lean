-- Prove2me | Theorems.Thm_MonotonicSolutions_CoreRules_coalitionallyMonotonic_iff_player
-- name    : MonotonicSolutions.CoreRules.coalitionallyMonotonic_iff_player
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T19:58:42.590507+00:00
-- url     : https://prove2.me/theorems/16f5234e-1a59-4f0f-b8b7-6780bfd81d9b
-- title:
--   Eq. (4) ⇔ Eq. (5): coalitional monotonicity equals its one-player form
-- statement:
--   Let $\varphi$ assign to each cooperative game $v$ on $N = \{1, \dots, n\}$ (with $v(\emptyset) = 0$) an allocation $\varphi(v) \in \mathbb{R}^N$. Then $\varphi$ is coalitionally monotonic in the sense of Eq. (4) if and only if the following holds: for every player $i$ and all games $v, w$,
--   $$\Big(v(S) \ge w(S) \text{ for all } S \ni i \ \text{ and } \ v(S) = w(S) \text{ for all } S \not\ni i\Big) \quad\Longrightarrow\quad \varphi_i(v) \ge \varphi_i(w). \tag{5}$$
--
--   Condition (5) says that a player whose alternatives (the coalitions containing him) all gain in value, while the coalitions not involving him stay fixed, does not lose. The equivalence lets the proof of Theorem 1 compare two games that differ on several coalitions at once.
--
--   **Formalization Note** Games range over `Game n` (functions vanishing at $\emptyset$) on both sides of the equivalence. No efficiency is assumed of $\varphi$.
-- source:
--   Young, Monotonic Solutions of Cooperative Games, Int. J. Game Theory 14 (1985), p. 68, Eqs. (4) and (5)

import Mathlib
import Definitions.Def_MonotonicSolutions_CoreRules_Game
import Definitions.Def_MonotonicSolutions_CoreRules_IsCoalitionallyMonotonic

namespace MonotonicSolutions.CoreRules

theorem coalitionallyMonotonic_iff_player {n : ℕ} (φ : Game n → Fin n → ℝ) :
    IsCoalitionallyMonotonic φ ↔
      ∀ (i : Fin n) (v w : Game n), (∀ S : Finset (Fin n), i ∈ S → w.1 S ≤ v.1 S) →
        (∀ S : Finset (Fin n), i ∉ S → v.1 S = w.1 S) → φ w i ≤ φ v i := by sorry

end MonotonicSolutions.CoreRules
