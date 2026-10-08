-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_6
-- name    : GTWSched.NPC.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:27.593985+00:00
-- url     : https://prove2.me/theorems/46780163-3afb-4717-9469-7d86296dd379
-- title:
--   LEMMA 6, p. 335 — in a minimum cost bracket schedule {Aᵢ, Bᵢ} = {T₂ᵢ, T₂ᵢ₋₁}
-- statement:
--   In the special case (tasks $T_0,\dots,T_{2n}$ with $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M>\sum_{i=0}^{2n}l_i$):
--
--   **LEMMA 6.** If $S=[A_n,A_{n-1},\dots,A_1,T_0@M,B_1,B_2,\dots,B_n]$ is a minimum cost schedule, then for every $i$, $1\le i\le n$,
--   $$\{A_i,B_i\}=\{T_{2i},T_{2i-1}\}.$$
--   So in an optimal schedule the $i$-th tasks on either side of $T_0$ are the $i$-th pair of lengths.
--
--   **Formalization Note** The bracket is given by injective maps `A B : Fin n → Fin (2n+1)` with disjoint ranges avoiding $T_0$ (index `0`); for the 0-based $k=i-1$ the conclusion is `{A k, B k} = {evenTask k, oddTask k}`, the indices $2k+2$ and $2k+1$. The bracket schedule is packed against $T_0$, which is the minimum cost schedule with that order and $T_0$ at $M$.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 335, LEMMA 6

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 6, p. 335: if `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]` is a minimum cost schedule, then
`{Aᵢ, Bᵢ} = {T₂ᵢ, T₂ᵢ₋₁}` for every `i` (0-based `i`: the tasks `2i + 2` and `2i + 1`). -/
theorem lemma_6 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (A B : Fin n → Fin (2 * n + 1))
    (hAB : IsBracket A B) (hmin : IsMinCost l M (centered l M A B)) (i : Fin n) :
    ({A i, B i} : Finset (Fin (2 * n + 1))) = {evenTask i, oddTask i} := by sorry

end GTWSched.NPC
