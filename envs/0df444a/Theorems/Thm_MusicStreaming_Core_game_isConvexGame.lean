-- Prove2me | Theorems.Thm_MusicStreaming_Core_game_isConvexGame
-- name    : MusicStreaming.Core.game_isConvexGame
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:31.377274+00:00
-- url     : https://prove2.me/theorems/24f299b9-6bb5-4fa5-95d6-78118e3e815b
-- title:
--   §4, p. 13 — the streaming game $v$ is a convex (supermodular) game
-- statement:
--   Let $(N,M,t)$ be a streaming problem with streaming game $v(S)=|\{j\in M:L^j\subseteq S\}|$. Then $v$ is a **convex game**: $v(\emptyset)=0$ and $v$ is supermodular,
--   $$v(S)+v(S')\le v(S\cup S')+v(S\cap S')\qquad\text{for all } S,S'\subseteq N.$$
--
--   Convexity means that the incentive to join a coalition grows with the coalition; it guarantees in particular that the core of the streaming game is nonempty and large.
--
--   **Formalization Note** Convexity is the published `Supermodularity.Cooperative.IsConvexGame`, which includes $v(\emptyset)=0$. The paper asserts the claim without proof; it is not used in the proof of Theorem 2.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 13, §4, last paragraph

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_IsConvexGame
import Definitions.Def_MusicStreaming_Core_Setting

namespace MusicStreaming.Core

/-- §4, p. 13: the streaming game is a convex game: `v(∅) = 0` and `v` is supermodular,
`v(S) + v(S') ≤ v(S ∪ S') + v(S ∩ S')`. -/
theorem game_isConvexGame {n : ℕ} (t : MusicStreaming.Axioms.Problem n) :
    Supermodularity.Cooperative.IsConvexGame (game t) := by sorry

end MusicStreaming.Core
