-- Prove2me | Theorems.Thm_MusicStreaming_CoreSelection_userCentric_mem_allocSet
-- name    : MusicStreaming.CoreSelection.userCentric_mem_allocSet
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T05:14:34.113952+00:00
-- url     : https://prove2.me/theorems/aab5dcd6-3486-4bb4-bb10-f85528defc9f
-- title:
--   §4, p. 14 — the user-centric rewards belong to A(N, M, t)
-- statement:
--   Let $(N, M, t)$ be any streaming problem, $U$ the user-centric index and $R^U$ the rewards it induces. Then
--   $$
--   R^U(N,M,t) \in A(N,M,t),
--   $$
--   that is, $R^U = \sum_{j \in M} x^j$ for vectors $x^j \in \mathbb R^N$ that are nonnegative, vanish outside the list $L^j$ of artists user $j$ played, and sum to $1$.
--
--   In words: the user-centric index splits each user's payment of $1$ among the artists that user played. Combined with Theorem 2 this places the user-centric rewards in the core of the streaming game.
--
--   **Formalization Note** The statement covers every problem, including the empty one ($M = \emptyset$), where both sides are the zero vector. Users are natural numbers and a problem is a finitely supported map from users to stream profiles.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 14, §4, paragraph after Theorem 2 ("by definition, the user-centric index yields … an allocation that belongs to A(N, M, t)")

import Mathlib
import Definitions.Def_Supermodularity_Cooperative_Core
import Definitions.Def_MusicStreaming_CoreSelection_Setting

namespace MusicStreaming.CoreSelection

/-- §4, p. 14: by definition, the user-centric index yields for every problem an allocation
(its rewards) that belongs to `A(N, M, t)`. -/
theorem userCentric_mem_allocSet (n : ℕ) (t : MusicStreaming.Axioms.Problem n) :
    MusicStreaming.Axioms.reward userCentric t ∈ MusicStreaming.Core.allocSet t := by sorry

end MusicStreaming.CoreSelection
