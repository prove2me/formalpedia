-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_4
-- name    : GTWSched.NPC.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:06.202603+00:00
-- url     : https://prove2.me/theorems/34d6613b-9605-48ba-b462-42d1eb42e99b
-- title:
--   LEMMA 4, p. 334 — in a minimum cost schedule the shortest task T₀ has its midtime at M
-- statement:
--   **LEMMA 4.** In the special case (tasks $T_0,\dots,T_{2n}$ with $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M>\sum_{i=0}^{2n}l_i$), if $S$ is a minimum cost schedule then
--   $$m_0(S)=M.$$
--
--   **Formalization Note** Tasks are `Fin (2n+1)` and $T_0$ is index `0`; schedules have nonnegative starting times.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 334, LEMMA 4

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 4, p. 334: in the special case, a minimum cost schedule has `m₀(S) = M`. -/
theorem lemma_4 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : mid l s 0 = M := by sorry

end GTWSched.NPC
