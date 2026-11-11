-- Prove2me | Theorems.Thm_GroupIsoDepth_LowerBounds_lemma_5_10
-- name    : GroupIsoDepth.LowerBounds.lemma_5_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:40:28.149749+00:00
-- url     : https://prove2.me/theorems/9cf9e0e5-6fd9-4564-9ebb-c8a1f66ad69e
-- title:
--   Lemma 5.10 — over $\mathbb F_q$ there are at least $q^{r(2k-r)-2k}$ matrices of size $k\times k$ and rank exactly $r$
-- statement:
--   Let $\mathbb F_q$ be a finite field with $q$ elements and $0\le r\le k$. Then there are at least $q^{r(2k-r)-2k}$ matrices of size $k\times k$ over $\mathbb F_q$ of rank exactly $r$.
--
--   Differences from the source:
--   - encoding: k × k matrices of rank exactly r → hypothesis r ≤ k; reason: a k × k matrix has rank ≤ k; for r > k the count is 0 and the statement has no content in the paper
--   - encoding: F_q → any finite field F with q = Fintype.card F; reason: every finite field is some F_q
--   - encoding: q^{r(2k−r)−2k} → real zpow with exponent r(2k − r) − 2k computed in ℤ; reason: the exponent can be negative
-- source:
--   Grochow, Kardeş, Levet, Group Isomorphism: Depth-2½ Circuits and Lower Bounds, STOC 2027 submission (manuscript sha256 cd6cacd4…), Lemma 5.10 (p. 39, PDF 40)

import Mathlib

namespace GroupIsoDepth.LowerBounds

/-- Lemma 5.10 (printed p. 39, PDF 40). Over a finite field `F_q`, there are at least
`q^{r(2k−r)−2k}` matrices of size `k × k` and rank exactly `r` (for every rank `0 ≤ r ≤ k`). -/
theorem lemma_5_10 {F : Type*} [Field F] [Fintype F] (k r : ℕ) (hr : r ≤ k) :
    (Fintype.card F : ℝ) ^ ((r : ℤ) * (2 * k - r) - 2 * k) ≤
      (Nat.card {M : Matrix (Fin k) (Fin k) F // M.rank = r} : ℝ) := by sorry

end GroupIsoDepth.LowerBounds
