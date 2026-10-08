-- Prove2me | Theorems.Thm_GTWSched_NPC_min_cost_no_gaps
-- name    : GTWSched.NPC.min_cost_no_gaps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:35:13.027965+00:00
-- url     : https://prove2.me/theorems/f953e1d3-ab5c-4b31-99de-6eb964232d07
-- title:
--   §2.1, p. 333 — a minimum cost schedule with a common preferred midtime has no gaps
-- statement:
--   Consider tasks $T_0,T_1,\dots,T_{2n}$ with lengths $0<l_0<l_1<\dots<l_{2n}$ and one common preferred midtime $M>\sum_{i=0}^{2n}l_i$, with cost $\mathrm{cost}(S)=\sum_{i=0}^{2n}|M-m_i(S)|$. If $S$ is a minimum cost schedule, then $S$ has no gaps between tasks:
--   $$\text{every task of }S\text{ either starts first or starts when another task finishes.}$$
--
--   This is the first structural property of optimal schedules used in the proof of THEOREM 1.
--
--   **Formalization Note** Tasks are `Fin (2n+1)`, $T_0$ is index `0`; schedules have nonnegative starting times (a standing assumption, which never binds when $M>\sum l_i$).
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 333, §2.1, "The first observation we make …"

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 333: in the special case (tasks `T₀, …, T₂ₙ` with `0 < l₀ < l₁ < ⋯ < l₂ₙ` and one common
preferred midtime `M > ∑ᵢ lᵢ`), a minimum cost schedule has no gaps between tasks. -/
theorem min_cost_no_gaps {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : NoGaps l s := by sorry

end GTWSched.NPC
