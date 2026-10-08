-- Prove2me | Theorems.Thm_GTWSched_NPC_min_cost_ordered
-- name    : GTWSched.NPC.min_cost_ordered
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:35:40.15399+00:00
-- url     : https://prove2.me/theorems/1f839715-8886-46d0-af57-bdb426b90787
-- title:
--   §2.1, p. 333 — a minimum cost schedule with a common preferred midtime is ordered
-- statement:
--   In the setting of the special case (tasks $T_0,\dots,T_{2n}$, $0<l_0<l_1<\dots<l_{2n}$, common preferred midtime $M>\sum_{i=0}^{2n}l_i$), every minimum cost schedule $S$ is **ordered**: with $A(S)=\{T_i:m_i(S)<M\}$ and $B(S)=\{T_i:m_i(S)>M\}$,
--   $$T_i,T_j\in A(S),\ l_i<l_j\ \Rightarrow\ m_i(S)>m_j(S),\qquad T_i,T_j\in B(S),\ l_i<l_j\ \Rightarrow\ m_i(S)<m_j(S).$$
--   Shorter tasks are scheduled nearer to $M$ on each side.
--
--   **Formalization Note** Tasks are `Fin (2n+1)`; schedules have nonnegative starting times.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 333, §2.1, "It is easy to show that for any minimum cost schedule …"

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 333: in the special case (tasks `T₀, …, T₂ₙ` with `0 < l₀ < l₁ < ⋯ < l₂ₙ` and one common
preferred midtime `M > ∑ᵢ lᵢ`), a minimum cost schedule is ordered. -/
theorem min_cost_ordered {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : Ordered l M s := by sorry

end GTWSched.NPC
