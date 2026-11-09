-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_boundary_path_identity
-- name    : OnlineSteinitz.Reduction.boundary_path_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:04.573537+00:00
-- url     : https://prove2.me/theorems/59a97da1-53dd-4a73-ad77-67d6e103f437
-- title:
--   Lemma 2.2 — one-boundary-path identity
-- statement:
--   For any completed output $w$ of horizon $T\ge1$ and any prefix $0\le k\le T$, let $P(k)$, $\alpha_{u,k}$ and $\operatorname{err}_u$ be the position-tree objects defined above. Then
--   $$\operatorname{res}_k(w)=\sum_{u\in P(k)}\alpha_{u,k}\operatorname{err}_u.$$
--   This exact identity allows global proportional-prefix residuals to be expressed in terms of the actual local splits. Both endpoint prefixes are included; no unit-ball or zero-total hypothesis is needed.
--
--   Differences from the source:
--   - encoding: positions and arrivals indexed from 1 → zero-based slots and arrivals, with half-open intervals [a,a+m); reason: subtracting one from indices preserves every input and prefix, including k=0,T; values outside the first T slots are ignored
--   - generalization: an arbitrary fixed norm on real finite-dimensional vector space → an arbitrary real normed space in the algebraic and norm/count clauses; reason: the same finite sums and triangle inequalities apply; every norm on real d-dimensional space is an instance, with no completeness hypothesis
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, Lemma 2.2, p.7, equation (2.6)

import Definitions.Def_OnlineSteinitz_Reduction_Analysis

open scoped BigOperators

namespace OnlineSteinitz.Reduction

/-- Lemma 2.2, p.7, (2.6). Arbitrary real normed spaces are a generalization
of the source's real finite-dimensional space; no boundedness is needed. -/
theorem boundary_path_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℕ) (hT : 0 < T) (w : ℕ → E) (k : ℕ) (hk : k ≤ T) :
    residual T w k = ∑ u ∈ boundaryPath T k, alpha u k • splitError w u := by sorry

end OnlineSteinitz.Reduction
