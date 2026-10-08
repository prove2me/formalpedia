-- Prove2me | Theorems.Thm_GTWSched_NPC_cost_ge_k_and_eq_case
-- name    : GTWSched.NPC.cost_ge_k_and_eq_case
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T07:49:31.853593+00:00
-- url     : https://prove2.me/theorems/727dd607-6732-4306-92c4-38e79e3e52d1
-- title:
--   Proof of THEOREM 1, p. 336 — every schedule of T₀, …, T₂ₙ costs at least k, and equality forces the optimal form
-- statement:
--   Let $T_0,\dots,T_{2n}$ have lengths $0<l_0<l_1<\dots<l_{2n}$ and the common preferred midtime $M=\frac12\sum_{i=0}^{2n}l_i$ used in the construction of $D$, and let
--   $$k=\sum_{i=1}^n(l_{2i}+l_{2i-1})\left(n-i+\tfrac12\right)+l_0\,n .$$
--   For every schedule $S$ of these tasks (nonnegative starting times, no overlaps):
--   1. $\mathrm{cost}(S)=\sum_{i=0}^{2n}|M-m_i(S)|\ge k$;
--   2. If $\mathrm{cost}(S)=k$, then $S$ is ordered, has no gaps, has $m_0(S)=M$, and for each $i$, $1\le i\le n$, exactly one of $T_{2i},T_{2i-1}$ is in $A(S)$ and the other is in $B(S)$.
--
--   This is the form in which the proof of THEOREM 1 uses Lemmas 2–6 and the minimum cost formula.
--
--   **Formalization Note** The midtime is fixed to the value used in $D$. The earlier special case assumes $M>\sum_i l_i$; this proof step applies its cost bound and necessary equality conditions at $M=\sum_i l_i/2$. For the 0-based $k'=i-1$, $T_{2i-1}$ and $T_{2i}$ are `oddTask k'` and `evenTask k'`.
-- source:
--   Garey, Tarjan & Wilfong, One-Processor Scheduling with Symmetric Earliness and Tardiness Penalties, Math. Oper. Res. 13 (1988), p. 336, proof of THEOREM 1

import Mathlib
import Definitions.Def_GTWSched_NPC_Schedules

namespace GTWSched.NPC

/-- p. 336, proof of THEOREM 1: at the constructed common preferred midtime
`M = (∑ᵢ lᵢ)/2`, every schedule of `T₀, …, T₂ₙ` costs at least `k`. A schedule of cost
exactly `k` is ordered, has no gaps, has `m₀(S) = M`, and places one task of each pair on
either side of `M`. -/
theorem cost_ge_k_and_eq_case {n : ℕ} (l : Fin (2 * n + 1) → ℝ) (M : ℝ) (hl0 : 0 < l 0)
    (hmono : StrictMono l) (hM : M = (∑ i, l i) / 2)
    (s : Fin (2 * n + 1) → ℝ) (hs : IsSchedule l s) :
    kStar l ≤ commonCost l M s ∧
      (commonCost l M s = kStar l →
        Ordered l M s ∧ NoGaps l s ∧ mid l s 0 = M ∧
          ∀ i : Fin n,
            (oddTask i ∈ setA l M s ∧ evenTask i ∈ setB l M s) ∨
              (evenTask i ∈ setA l M s ∧ oddTask i ∈ setB l M s)) := by sorry

end GTWSched.NPC
