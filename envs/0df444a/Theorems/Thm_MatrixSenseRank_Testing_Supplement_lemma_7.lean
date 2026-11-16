-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_lemma_7
-- name    : MatrixSenseRank.Testing.Supplement.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:09:47.687308+00:00
-- url     : https://prove2.me/theorems/8476b54a-a49a-4ebc-a62b-5d44f2198f70
-- title:
--   Lemma 7 — geometry of the rank-two prior
-- statement:
--   Let $n\ge2$ and let $A$ belong to the topological support of $D_{\rm no}$ from Definition 6. Then
--
--   $$\|A\|_F=1,\qquad\operatorname{rank}(A)=2,\qquad\|A-B\|_F\ge\sqrt{2-\sqrt2}$$
--
--   for every matrix $B\in\mathbb R^{n\times n}$ with rank one and Frobenius norm one. The quantified comparison matrices are arbitrary real matrices, without symmetry or positivity restrictions.
--
--   This identifies the no-prior as valid far-from-rank-one inputs for Theorem 1.
--
--   Differences from the source:
--   - encoding: finite real Euclidean matrices with the paper's Frobenius norm → matrices indexed by Fin n and Fin m, with the published Frobenius and normalized-distance definitions; reason: a change of coordinates and indexing only; positive dimensions are retained
--   - encoding: uniform sphere and Haar orthonormal pair → Gaussian normalization and Gram–Schmidt pushforward laws; reason: these construct the same probability laws for n at least two; null exceptional inputs have no effect
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Lemma 7, printed p. 14, PDF p. 15 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Priors

set_option autoImplicit false

namespace MatrixSenseRank.Testing.Supplement

/-- Lemma 7, printed p.14 / PDF p.15. Topological support, not merely almost surely. -/
theorem lemma_7 (n : ℕ) (hn : 2 ≤ n) (A : Mat n n)
    (hA : A ∈ (noPrior n).support) :
    frobenius A = 1 ∧ A.rank = 2 ∧
      ∀ B : Mat n n, B.rank = 1 → frobenius B = 1 →
        Real.sqrt (2 - Real.sqrt 2) ≤ frobenius (A - B) := by sorry

end MatrixSenseRank.Testing.Supplement
