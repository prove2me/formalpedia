-- Prove2me | Theorems.Thm_LambdaCoalescent_Rates_lemma_18_consistent_iff
-- name    : LambdaCoalescent.Rates.lemma_18_consistent_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:59.746029+00:00
-- url     : https://prove2.me/theorems/7a8cdaf0-400f-4a28-ab3f-86658ace14ec
-- title:
--   Lemma 18 — consistency iff adjacent merger rates add
-- statement:
--   Let $\lambda_{b,k}\ge0$ be the rate for each unordered $k$-tuple of blocks to merge when there are $b$ blocks, for $2\le k\le b$. The associated finite coalescent chains are consistent under restriction exactly when
--
--   $$
--   \lambda_{b,k}=\lambda_{b+1,k}+\lambda_{b+1,k+1}\qquad(2\le k\le b).
--   $$
--
--   This local identity is the rate-level criterion behind the existence characterization in Theorem 1.
--
--   **Formalization Note** Consistency is expressed by equality of the finite chains’ semigroup transition probabilities after restriction, for all times and initial states.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1882, Lemma 18, eq. (22)

import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

/-- Lemma 18, p. 1882, equivalence (22). -/
theorem lemma_18_consistent_iff (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k) :
    Consistent lam ↔
      ∀ b k, 2 ≤ k → k ≤ b →
        lam b k = lam (b + 1) k + lam (b + 1) (k + 1) := by sorry

end LambdaCoalescent.Rates
