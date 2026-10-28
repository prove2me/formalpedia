-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_userCentric_reward_mem_core
-- name    : MusicStreaming.CoreSelection.userCentric_reward_mem_core
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:42.06951+00:00
-- url     : https://prove2.me/theorems/1158b2cb-5f71-4952-883d-0caad01db7ed
-- title:
--   §4, p. 14 — the user-centric rewards always belong to the core of the streaming game
-- statement:
--   Let $(N, M, t)$ be any streaming problem and $v(S) = |\{j \in M : L^j \subseteq S\}|$ its streaming game on the artists. The rewards induced by the user-centric index $U_i = \sum_{j\in M} t_{ij}/T^j$ lie in the core of $v$:
--   $$
--   R^U(N,M,t) \in C(N,v) = \Big\{ x \in \mathbb R^N : \sum_{i\in N} x_i = v(N),\ \sum_{i \in S} x_i \ge v(S) \text{ for all } S \subseteq N \Big\}.
--   $$
--
--   This is the observation that motivates the axiom of core selection: no coalition of artists can claim more than the user-centric index pays it, if a coalition's claim is the payment of the users who only played its members.
--
--   **Formalization Note** The statement holds on every problem, not only on $\mathcal P^*$, as printed. The paper obtains it from Theorem 2 ($C(N,v) = A(N,M,t)$); that theorem is drafted in a sibling mission and cannot be imported, so this consequence is stated here on its own.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 14, §4, paragraph after Theorem 2 ("by Theorem 2, the rewards induced by the user-centric index always belong to the core")

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- §4, p. 14: the rewards induced by the user-centric index always belong to the core
`C(N, v)` of the streaming game, on every problem. -/
theorem userCentric_reward_mem_core (n : ℕ) (t : MusicStreaming.Axioms.Problem n) :
    MusicStreaming.Axioms.reward userCentric t ∈ Supermodularity.Cooperative.Core Finset.univ (MusicStreaming.Core.game t) := by sorry

end MusicStreaming.CoreSelection
