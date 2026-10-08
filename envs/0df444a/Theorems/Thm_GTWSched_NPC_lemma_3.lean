-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_3
-- name    : GTWSched.NPC.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:37:33.649509+00:00
-- url     : https://prove2.me/theorems/07ee8014-eced-496b-920e-035bd02d4112
-- title:
--   LEMMA 3, p. 334 — in a minimum cost schedule |A(S)| = |B(S)|
-- statement:
--   **LEMMA 3.** In the special case (tasks $T_0,\dots,T_{2n}$ with $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M>\sum_{i=0}^{2n}l_i$), if $S$ is a minimum cost schedule then
--   $$|A(S)|=|B(S)|,$$
--   where $A(S)=\{T_i:m_i(S)<M\}$ and $B(S)=\{T_i:m_i(S)>M\}$: as many tasks have their midtimes before $M$ as after.
--
--   **Formalization Note** Tasks are `Fin (2n+1)`; $A(S)$, $B(S)$ are `Finset`s of indices; schedules have nonnegative starting times.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 334, LEMMA 3

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 3, p. 334: in the special case, a minimum cost schedule has `|A(S)| = |B(S)|`. -/
theorem lemma_3 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : (setA l M s).card = (setB l M s).card := by sorry

end GTWSched.NPC
