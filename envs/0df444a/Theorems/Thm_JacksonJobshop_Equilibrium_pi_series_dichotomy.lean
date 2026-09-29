-- Prove2me | Theorems.Thm_JacksonJobshop_Equilibrium_pi_series_dichotomy
-- name    : JacksonJobshop.Equilibrium.pi_series_dichotomy
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T15:13:23.472685+00:00
-- url     : https://prove2.me/theorems/84b569db-84b4-42af-8647-b02a98c37a81
-- title:
--   §4, after (4.4) — the series defining $\pi$ converges to a positive number or diverges to $+\infty$
-- statement:
--   Let $(N, L, M, R)$ be a jobshop-like queueing system satisfying Assumptions (2.1)–(2.4), and let $W(K) = \prod_{i=0}^{K-1}\lambda(i)$ and $T(K) = \sum_{S(\bar k) = K} \prod_{n=1}^N \prod_{i=1}^{k_n} e(n)/\mu(n, i)$ be the quantities (4.1)–(4.3). Then the series
--   $$\sum_{K=0}^\infty W(K)\, T(K)$$
--   appearing in (4.4) either converges to a strictly positive number, or its partial sums diverge to $+\infty$.
--
--   This is what makes the normalising constant $\pi$ of (4.4) well defined: $\pi > 0$ exactly when the series converges, and $\pi = 0$ otherwise.
--
--   **Formalization Note** Both halves are stated: if $K \mapsto W(K)T(K)$ is summable then its sum is $> 0$; if it is not summable then the partial sums $\sum_{K < M} W(K)T(K)$ tend to $+\infty$ as $M \to \infty$.
-- source:
--   Jackson, Jobshop-Like Queueing Systems, Management Science 10(1) (1963), p. 136, §4, sentence after (4.4)

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System

namespace JacksonJobshop.Equilibrium

/-- Jackson (1963), p. 136, sentence after (4.4): the series `Σ_K W(K) T(K)` in (4.4) either
converges to a positive number or diverges to `+∞`. -/
theorem pi_series_dichotomy {N : ℕ} (sys : JobshopSystem N) :
    (Summable (fun K => W sys K * T sys K) → 0 < ∑' K, W sys K * T sys K) ∧
    (¬ Summable (fun K => W sys K * T sys K) →
      Filter.Tendsto (fun M => ∑ K ∈ Finset.range M, W sys K * T sys K)
        Filter.atTop Filter.atTop) := by sorry

end JacksonJobshop.Equilibrium
