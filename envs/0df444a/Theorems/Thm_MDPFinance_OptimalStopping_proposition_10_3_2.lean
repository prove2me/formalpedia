-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_proposition_10_3_2
-- name    : MDPFinance.OptimalStopping.proposition_10_3_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:33.149525+00:00
-- url     : https://prove2.me/theorems/a5db532b-c341-4c21-a5b2-b6424a6fdb44
-- title:
--   Proposition 10.3.2 — the secretary problem's value function in closed form
-- statement:
--   **Proposition 10.3.2** (p. 322). We claim now that for $n = 0,\dots,N-1$:
--
--   $$ V_n(x) = \begin{cases} 1, & x = N \\ \dfrac{x}{N}, & x = k^*+1,\dots,N-1 \\
--   \dfrac{k^*}{N}h(k^*), & x = n,\dots,k^*. \end{cases} $$
--
--   The secretary problem solved in closed form. The three branches are the three regimes: at the last
--   possible leading position the best candidate is certainly the current one; above the threshold
--   $k^*$ the value is the probability $x/N$ that the current leader is the overall best, so it is
--   optimal to stop; at or below $k^*$ the value is the constant $\frac{k^*}{N}h(k^*)$, independent of
--   $x$, which is exactly the statement that in that range one should keep going.
--
--   $h$ and $k^*$ are the book's own: $h(x) = \frac1x + \frac1{x+1} + \dots + \frac1{N-1}$ and
--   $k^* = \inf\{k \in \{1,\dots,N-2\} \mid h(k) > 1 \ge h(k+1)\}$ **(10.5)**, both on p. 322. They are
--   not free parameters and the proposition is false for an arbitrary $k$.
--
--   The third branch's range starts at $n$, not at $1$: $V_n$ is only meaningful for $x \ge n$, since
--   $X_n$ takes values in $\{n+1,\dots,N+1\}$.
--
--   **Moderation note.** The third branch was stated for `x = n,…,k^*` including `x = 0` when `n = 0`, where `V_0(0) = 0 ≠ (k^*/N)h(k^*)` (refutable; `0` is not a state). Now `1 ≤ x`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 322 (PDF 330), Proposition 10.3.2

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

namespace MDPFinance.OptimalStopping

/-- **Proposition 10.3.2** (p. 322). For `n = 0,…,N-1` and states `x ∈ {1,…,N}`:
`V_n(x) = 1` if `x = N`; `= x/N` if `x = k^*+1,…,N-1`; `= (k^*/N) h(k^*)` if `x = n,…,k^*`
(with `x ≥ 1`, the states of the chain). -/
theorem proposition_10_3_2 (S : Secretary) (n : ℕ) (hn : n < S.N) :
    (S.V n S.N = 1) ∧
    (∀ x : ℕ, S.kStar + 1 ≤ x → x ≤ S.N - 1 → S.V n x = (x : ℝ) / (S.N : ℝ)) ∧
    (∀ x : ℕ, 1 ≤ x → n ≤ x → x ≤ S.kStar →
      S.V n x = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar) := by sorry

end MDPFinance.OptimalStopping
