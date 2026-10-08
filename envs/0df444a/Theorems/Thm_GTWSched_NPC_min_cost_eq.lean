-- Prove2me | Theorems.Thm_GTWSched_NPC_min_cost_eq
-- name    : GTWSched.NPC.min_cost_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:41:54.515698+00:00
-- url     : https://prove2.me/theorems/258190b2-5f77-433e-ae5d-703077f97742
-- title:
--   §2.1, p. 336 — the cost of a minimum cost schedule is Σᵢ(l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n
-- statement:
--   In the special case (tasks $T_0,\dots,T_{2n}$ with $0<l_0<l_1<\dots<l_{2n}$ and common preferred midtime $M>\sum_{i=0}^{2n}l_i$), the cost of every minimum cost schedule $S$ is
--   $$\mathrm{cost}(S)=\sum_{i=1}^n\,(l_{2i}+l_{2i-1})\left(n-i+\tfrac12\right)+l_0\,n .$$
--
--   This value is the threshold $k$ of the instance D in the proof of THEOREM 1.
--
--   **Formalization Note** The right side is `kStar l`; with the 0-based $k=i-1$ its summand is $(l_{2k+2}+l_{2k+1})(n-k-\tfrac12)$.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336, §2.1, "Given the above characterization …"

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 336: in the special case, the cost of every minimum cost schedule is
`∑ᵢ₌₁ⁿ (l₂ᵢ + l₂ᵢ₋₁)(n − i + 1/2) + (l₀)n`. -/
theorem min_cost_eq {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : ∑ i, l i < M) (s : Fin (2 * n + 1) → ℝ)
    (hs : IsMinCost l M s) : commonCost l M s = kStar l := by sorry

end GTWSched.NPC
