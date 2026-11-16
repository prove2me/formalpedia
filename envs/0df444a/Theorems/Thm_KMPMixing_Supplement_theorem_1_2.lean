-- Prove2me | Theorems.Thm_KMPMixing_Supplement_theorem_1_2
-- name    : KMPMixing.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:56:24.862228+00:00
-- url     : https://prove2.me/theorems/ea6966aa-1d2b-4757-a6f9-7406d9203b78
-- title:
--   Theorem 1.2 (formal: Corollary 5.6) — coordinate hit-and-run on $S_n$ mixes in $O(n(\log n+\log(1/\varepsilon)))$ steps
-- statement:
--   Let $n\ge2$ and $S_n=\{x\in\mathbb R^n_{\ge0}:\sum_ix_i\le1\}$. Coordinate hit-and-run chooses $i\in[n]$ uniformly and replaces $x_i$ by a uniform sample from $[0,1-\sum_{j\ne i}x_j]$; let $\pi_n$ be the uniform distribution on $S_n$.
--
--   There is an absolute constant $C>0$ such that for every $n\ge2$ and every $\varepsilon\in(0,1)$ some $k\in\mathbb N$ with
--   $$
--   k\le C\,n\Big(\log n+\log\frac1\varepsilon\Big)
--   $$
--   satisfies $\|K^k(x,\cdot)-\pi_n\|_{\mathrm{TV}}\le\varepsilon$ for every initial point $x\in S_n$, where $K$ is the hit-and-run kernel. That is, the total-variation mixing time is $O(n(\log n+\log(1/\varepsilon)))$, uniformly over initial points.
--
--   This improves the bound obtained from general convex-body estimates for coordinate hit-and-run.
--
--   **Formalization Note** $C$ is quantified before $n$ and $\varepsilon$. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - reading: Theorem 1.2 (informal): mixes to within ε in O(n(log n + log(1/ε))) steps → the formal version Corollary 5.6 with the O(·) pinned as one absolute C > 0 quantified before n ≥ 2 and ε ∈ (0,1); reason: the paper labels Theorem 1.2 as the informal version of Corollary 5.6
--   - encoding: mixing time at most B, from any initial distribution → some k ∈ ℕ with k ≤ B has ‖K^k(x,·) − π_n‖_TV ≤ ε for every x ∈ S_n; reason: the mixing time is the least such k; by convexity of the total variation distance the worst initial distribution is a point mass
-- source:
--   Chen, Liu, Qin, Schulman, Song, Yao, Zhao, A Tale of Two Walks: From Kac to KMP and Back, arXiv:2609.38044 (sha256 6a9abdd4…), Theorem 1.2, p.4 (PDF p.6); formal version Corollary 5.6, p.38 (PDF p.40), with §5.3's definition of the walk and Remark 5.7, p.39

import Mathlib
import Definitions.Def_KMPMixing_Supplement_hitAndRun

namespace KMPMixing.Supplement

/-- **Theorem 1.2** (arXiv:2609.38044, p.4 (PDF p.6)), stated at the strength of its formal
version **Corollary 5.6** (p.38 (PDF p.40)). There is an absolute constant `C > 0` such that for
every integer `n ≥ 2` and every `ε ∈ (0, 1)`, the total-variation mixing time of coordinate
hit-and-run on the standard simplex `S_n = {x ∈ ℝ^n_{≥0} : Σ x_i ≤ 1}`, to the uniform
distribution `π_n` on `S_n`, is at most `C · n · (log n + log(1/ε))`, from every initial point.

**Formalization Note** `O(·)` is one absolute constant `C`, quantified before `n` and `ε`. "Mixing
time at most `B`" is stated as: some `k ∈ ℕ` with `k ≤ B` has `‖K^k(x, ·) − π_n‖_TV ≤ ε` for
every `x ∈ S_n` (from any initial distribution by convexity). `log` is the natural logarithm. -/
theorem theorem_1_2 :
    ∃ C : ℝ, 0 < C ∧
      ∀ n : ℕ, 2 ≤ n →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
        ∃ k : ℕ, (k : ℝ) ≤ C * n * (Real.log n + Real.log (1 / ε)) ∧
          ∀ x ∈ hitSimplex n,
            tvMeasure (kernelLaw (hitAndRunKernel n) k x) (hitUniform n) ≤ ε := by sorry

end KMPMixing.Supplement
