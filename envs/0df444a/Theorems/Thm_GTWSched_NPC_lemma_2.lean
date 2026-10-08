-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_2
-- name    : GTWSched.NPC.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:36:03.705652+00:00
-- url     : https://prove2.me/theorems/15024de8-c682-46a3-a27e-ba8ecff1c1b3
-- title:
--   LEMMA 2, p. 334 — in a minimum cost schedule some task has its midtime at M
-- statement:
--   **LEMMA 2.** In the special case (tasks $T_0,\dots,T_{2n}$ with $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M>\sum_{i=0}^{2n}l_i$), if $S$ is a minimum cost schedule then
--   $$m_i(S)=M\quad\text{for some } i,\ 0\le i\le 2n.$$
--
--   **Formalization Note** Tasks are `Fin (2n+1)`; schedules have nonnegative starting times.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 334, LEMMA 2

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 2, p. 334: in the special case, a minimum cost schedule has some task with its midtime
at `M`. -/
theorem lemma_2 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : ∃ i, mid l s i = M := by sorry

end GTWSched.NPC
