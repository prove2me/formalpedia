-- Prove2me | Theorems.Thm_GTWSched_NPC_lemma_5
-- name    : GTWSched.NPC.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:23.151897+00:00
-- url     : https://prove2.me/theorems/a162a31c-41f0-49e8-a145-61053acb8a17
-- title:
--   LEMMA 5, p. 335 — swapping Aᵢ and Bᵢ in [Aₙ, …, A₁, T₀@M, B₁, …, Bₙ] keeps the cost
-- statement:
--   Let $T_0,\dots,T_{2n}$ have lengths $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M$. For a schedule
--   $$S=[A_n,A_{n-1},\dots,A_1,T_0@M,B_1,B_2,\dots,B_n]$$
--   ($T_0$ with midtime $M$, the $B$'s after it and the $A$'s before it in the indicated order, packed without gaps) and $1\le i\le n$, let $S_i=[A_n,\dots,A_{i+1},B_i,A_{i-1},\dots,A_1,T_0@M,B_1,\dots,B_{i-1},A_i,B_{i+1},\dots,B_n]$ be the schedule obtained by swapping $A_i$ and $B_i$.
--
--   **LEMMA 5.** $$\mathrm{cost}(S_i)=\mathrm{cost}(S).$$
--
--   **Formalization Note** The bracket is given by injective maps `A B : Fin n → Fin (2n+1)` with disjoint ranges avoiding $T_0$; `A k` is the paper's $A_{k+1}$, and $S_i$ is obtained by updating `A` at $i$ to `B i` and `B` at $i$ to `A i`. The common midtime satisfies $M>\sum_i l_i$, and $S$ is a minimum cost schedule, as in the surrounding special case.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 335, LEMMA 5 (Sᵢ defined on p. 335)

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- LEMMA 5, p. 335: swapping `Aᵢ` and `Bᵢ` in `[Aₙ, …, A₁, T₀@M, B₁, …, Bₙ]` does not change the
cost. -/
theorem lemma_5 {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M)
    (A B : Fin n → Fin (2 * n + 1)) (hAB : IsBracket A B)
    (hmin : IsMinCost l M (centered l M A B)) (i : Fin n) :
    commonCost l M (centered l M (Function.update A i (B i)) (Function.update B i (A i))) =
      commonCost l M (centered l M A B) := by sorry

end GTWSched.NPC
