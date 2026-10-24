-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_proposition_1
-- name    : NonprofitFunds.Capacity.proposition_1
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:10.637371+00:00
-- url     : https://prove2.me/theorems/657461a8-3520-4a7a-966c-ac550ecb1016
-- title:
--   Proposition 1, pp. 12–13 (PDF 12–13) — capacity thresholds k^l ≤ k^h: expand and exhaust below k^l, exhaust between, leave capacity unused above k^h
-- statement:
--   Fix the data $(r,B_1,\psi_1,m,\delta,\phi,\mu)$ under the standing assumptions, and let the first-period capacity $k_1$ vary over the admissible range $k_1\ge 0$, $B_1\ge 2m(k_1)$. Problem (2) has an optimal allocation for every admissible $k_1$, and there are two thresholds $k^l\le k^h$ such that every optimal allocation $(p^*_1,a^*_1,f^*_1)$ of problem (2), with $k_2=k_1+\delta(a^*_1)$ and $\hat B_2=D(p^*_1,a^*_1,f^*_1)-m(k_2)$, satisfies:
--   1. (a) if $k_1<k^l$: the nonprofit expands capacity and exhausts it,
--   $$a^*_1>0,\qquad (r+1)\hat B_2=k_2;$$
--   2. (b) if $k^l\le k_1<k^h$: the second-period capacity is exhausted, $(r+1)\hat B_2=k_2$, and if the program ceiling does not bind, $p^*_1<\theta/(r+1)$, then $a^*_1=0$;
--   3. (c) if $k_1\ge k^h$: $a^*_1=0$ (so $k_2=k_1$) and $(r+1)\hat B_2\le k_2$, with $(r+1)\hat B_2<k_2$ when $k_1>k^h$.
--
--   In words: a nonprofit with low capacity spends on administration to grow and then fills the larger capacity; at moderate capacity it does not grow (unless the program ceiling binds) but still fills its capacity; at high capacity it leaves capacity unused. Starving administration is optimal only in the last regime.
--
--   **Formalization Note.** The page speaks of "the optimal" allocation; the statement asserts existence and then quantifies over every optimal allocation. Three boundary repairs are made. At $k_1=k^h$ the optimum lies on constraint (2f), so (c) gives $(r+1)\hat B_2\le k_2$ there and the strict inequality only for $k_1>k^h$. In (b), the page's case (i) "$p^*_1=\theta/(r+1)$ implies $a^*_1>0$" fails when $\theta/(r+1)$ coincides with $p^+_u$ (then $a^*_1=0$), so only case (ii) is asserted. The thresholds are fixed before $k_1$ varies.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), pp. 12–13 (PDF 12–13), Proposition 1; proof pp. S12–S14 (PDF 41–43)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Proposition 1, pp. 12–13: problem (2) has an optimal allocation for every admissible `k1`, and
there are thresholds `k^l ≤ k^h` such that every optimal allocation `(p*1, a*1, f*1)` satisfies:
(a) `k1 < k^l`: `a*1 > 0` and `(r + 1) B̂2 = k2`;
(b) `k^l ≤ k1 < k^h`: `(r + 1) B̂2 = k2`, and `a*1 = 0` when `p*1 < θ/(r + 1)`;
(c) `k1 ≥ k^h`: `a*1 = 0` and `(r + 1) B̂2 ≤ k2`, strictly when `k1 > k^h`. -/
theorem proposition_1 (P : Params) (hP : P.Standing) :
    (∀ k1, P.Admissible k1 → ∃ p a f, P.IsOptimal2 k1 p a f) ∧
    ∃ kl kh : ℝ, kl ≤ kh ∧ ∀ k1, P.Admissible k1 → ∀ p a f, P.IsOptimal2 k1 p a f →
      (k1 < kl → 0 < a ∧ (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a) ∧
      (kl ≤ k1 → k1 < kh →
        (P.r + 1) * P.Bhat2 k1 p a f = k1 + P.delta a ∧ ((P.r + 1) * p < P.theta k1 → a = 0)) ∧
      (kh ≤ k1 → a = 0 ∧ (P.r + 1) * P.Bhat2 k1 p a f ≤ k1) ∧
      (kh < k1 → (P.r + 1) * P.Bhat2 k1 p a f < k1) := by sorry

end NonprofitFunds.Capacity
