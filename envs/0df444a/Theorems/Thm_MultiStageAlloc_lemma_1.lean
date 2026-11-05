-- Prove2me | Theorems.Thm_MultiStageAlloc_lemma_1
-- name    : MultiStageAlloc.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:30:34.9057+00:00
-- url     : https://prove2.me/theorems/a5d763a4-4208-47c1-b771-9a682b3cf95e
-- title:
--   Lemma 1 — the telescoping bound on the polynomial regularizers
-- statement:
--   Let $K\in\mathbb N$, $k\in[K-1]$, $x\in[0,1]$, and let $0=y_1\le y_2\le\dots\le y_k\le 1-x$. Then
--   $$
--   (1-x)f_k(y_k+x)-\sum_{s=1}^{k-1}(y_{s+1}-y_s)f_s(y_{s+1})\le 1-\Gamma(K)=\Bigl(1-\frac1K\Bigr)^K .
--   $$
--   This is the technical inequality that yields inequality (1), and it is reused for configuration allocation in the source.
--
--   Differences from the source:
--   - encoding: a finite sequence y_1, …, y_k → y : ℕ → ℝ of which only y_1, …, y_k enter; reason: same instances
-- source:
--   Feng & Niazadeh, Batching and Optimal Multi-stage Bipartite Allocations, arXiv:2211.16581v1, Lemma 1, p.22

import Mathlib
import Definitions.Def_MultiStageAlloc_Regularizers

namespace MultiStageAlloc

/-- **Lemma 1.** Feng & Niazadeh, arXiv:2211.16581v1, p.22. For `k ∈ [K - 1]`, `x ∈ [0, 1]` and
`0 = y_1 ≤ y_2 ≤ ⋯ ≤ y_k ≤ 1 - x`,
`(1 - x) f_k(y_k + x) - ∑_{s=1}^{k-1} (y_{s+1} - y_s) f_s(y_{s+1}) ≤ 1 - Γ(K) = (1 - 1/K)^K`.
The sequence is `y : ℕ → ℝ`, of which only `y 1, …, y k` enter. -/
theorem lemma_1 (K k : ℕ) (hk1 : 1 ≤ k) (hkK : k < K) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (y : ℕ → ℝ) (hy1 : y 1 = 0) (hmono : ∀ s, 1 ≤ s → s < k → y s ≤ y (s + 1))
    (hyk : y k ≤ 1 - x) :
    (1 - x) * regPoly K k (y k + x)
        - ∑ s ∈ Finset.Ico 1 k, (y (s + 1) - y s) * regPoly K s (y (s + 1)) ≤ 1 - gammaK K ∧
    1 - gammaK K = (1 - 1 / (K : ℝ)) ^ K := by sorry

end MultiStageAlloc
