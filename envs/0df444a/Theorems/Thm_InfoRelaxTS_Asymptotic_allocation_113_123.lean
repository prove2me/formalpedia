-- Prove2me | Theorems.Thm_InfoRelaxTS_Asymptotic_allocation_113_123
-- name    : InfoRelaxTS.Asymptotic.allocation_113_123
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:33.304709+00:00
-- url     : https://prove2.me/theorems/b8a25958-abc6-426d-81ad-0a1fd8ec54dc
-- title:
--   (113)–(123), §D.2, pp. 54–56 — for large T every optimal allocation gives most pulls to argmax_a v(a)
-- statement:
--   Let $m_{a,i}$ ($a \in \mathcal A = \{1,\dots,K\}$, $i \ge 0$) be a payoff table whose rows converge, $\lim_{i\to\infty} m_{a,i} = v(a)$ for every arm $a$, to limits $v(a)$ that are pairwise distinct. For a horizon $T$, call an allocation $n = (n_1,\dots,n_K) \in \mathcal N_T = \{n \in \mathbb N_0^K : \sum_a n_a = T\}$ *optimal* if it maximizes the inner payoff of IRS.V-Zero,
--   $$\sum_{a=1}^K \sum_{s=1}^{n_a} m_{a,s-1}$$
--   over $\mathcal N_T$ (cf. (37), (116)). Then there is $T_0$ such that for every $T \ge T_0$, every optimal allocation $n$ of horizon $T$, and every arm $b$ that receives the largest number of pulls ($n_c \le n_b$ for all $c$), the arm $b$ is the arm with the largest limit:
--   $$v(c) \le v(b) \qquad \text{for all } c \in \mathcal A.$$
--   In particular, for large $T$ the arm $\operatorname{argmax}_a \tilde n^*_a$ played by IRS.V-Zero is $\operatorname{argmax}_a v(a)$, whatever the tie-breaking rules in the inner problem and in the final argmax.
--
--   Applied with $m_{a,i} = \hat\mu_{a,i}(\tilde\omega)$ and $v(a) = \mu_a(\tilde\theta_a)$, together with Proposition 5, this is the exchange argument (113)–(123) of the proof of (56).
--
--   **Formalization Note.** This is the deterministic core of the argument, stated with an unspecified threshold $T_0$. The printed proof uses $T \ge 2N + 8MN/\Delta + 2$ and $n^\circ(A^\circ_T) \ge \lfloor T/2 \rfloor$. The second holds only for $K = 2$, since the largest of $K$ counts summing to $T$ is only guaranteed to be at least $\lceil T/K \rceil$. With $\lceil T/K\rceil$ in place of $\lfloor T/2\rfloor$ the printed Case 1/Case 2 argument goes through for a threshold that grows with $K$. The closing phrase "more than a half of the pulls" is likewise specific to $K = 2$. The "eventually in $T$" form is what (56) needs. The bound $M < \infty$ of (113) follows from convergence and is not a hypothesis. Arms are `Fin K` with $K \ge 1$.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, pp. 54–56, §D.2, (113)–(123)

import Mathlib
import Definitions.Def_InfoRelaxTS_Asymptotic_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace InfoRelaxTS.Asymptotic

/-- The allocation argument (113)–(123), §D.2, pp. 54–56, deterministic core: if every payoff
sequence `m a` converges to `v a` and the `v a` are pairwise distinct, then for all large `T`
every optimal allocation of the inner problem (37) gives its largest number of pulls only to the
arm maximizing `v`. -/
theorem allocation_113_123 {K : ℕ} [NeZero K] (m : Fin K → ℕ → ℝ) (v : Fin K → ℝ)
    (hv : Function.Injective v) (hm : ∀ a, Tendsto (m a) atTop (𝓝 (v a))) :
    ∀ᶠ T in atTop, ∀ n ∈ Gap.allocSet K T,
      (∀ n' ∈ Gap.allocSet K T, Gap.allocPayoff m n' ≤ Gap.allocPayoff m n) →
        ∀ b, (∀ c, n c ≤ n b) → ∀ c, v c ≤ v b := by sorry

end InfoRelaxTS.Asymptotic
