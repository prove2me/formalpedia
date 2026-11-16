-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_theorem_15
-- name    : MatrixSenseRank.Testing.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:52.63257+00:00
-- url     : https://prove2.me/theorems/8ef84a22-6de0-4964-80cc-e6ba02f99083
-- title:
--   Theorem 15 — exponential full-observation sparsity lower bound
-- statement:
--   There are absolute $c>0$, an integer $k_0\ge4$, and a dimension threshold $N(k)$ depending only on $k$ such that, for every $k\ge k_0$, every $n\ge\max\{k+1,N(k)\}$ and every $0<\varepsilon\le k^{-3/2}$, the following holds. A randomized test receives independent labeled examples
--
--   $$ (x,w\cdot x+\eta),\qquad x_i=G_iH_i,\qquad\eta\sim N(0,1), $$
--
--   where all Gaussian factors and the noise are independent standard normals and $w$ is any unknown signed unit vector. Suppose the test accepts with probability at least $9/10$ for every $k$-sparse $w$, and rejects with probability at least $9/10$ whenever the relative distance to $k$-sparse vectors is strictly greater than $\varepsilon$. Then
--
--   $$T\ge2^{ck}.$$
--
--   The test observes $x$ as well as the label. All constants and the function $N$ precede the target, test, accuracy and sample count. No claim about every small $k$ is added.
--
--   This is the companion sparsity result used in the reduction to the matrix lower bound. On unit vectors the published relative sparse distance equals ordinary Euclidean distance to the unrestricted-norm sparse approximants.
--
--   Differences from the source:
--   - encoding: finite-dimensional unit real vectors and relative sparse distance → Fin n vectors and the published vectorNorm, IsSparse and sparseDistance; reason: signed coefficients and arbitrary sparse approximant norms are retained
--   - encoding: possibly randomized algorithms observing full sample pairs → measurable Boolean probability kernels averaged under the actual independent sample law; reason: this represents all internal randomization without removing observed covariates
--   - encoding: absolute asymptotic constants and sufficiently large dimensions → existential constants and thresholds preceding every dimension, accuracy, sample count and test; reason: the constants are uniform; no numerical coefficient is invented
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Theorem 15, printed p. 28–29, PDF p. 29–30 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments

set_option autoImplicit false

namespace MatrixSenseRank.Testing.Supplement

/-- Theorem 15, printed pp.28--29 / PDF pp.29--30. All signed unit targets and the full pair are observed. -/
theorem theorem_15 :
    ∃ c : ℝ, 0 < c ∧ ∃ (k₀ : ℕ) (N : ℕ → ℕ), 4 ≤ k₀ ∧
      ∀ k n : ℕ, k₀ ≤ k → max (k + 1) (N k) ≤ n →
        ∀ ε : ℝ, 0 < ε → ε ≤ accuracyScale k →
          ∀ (T : ℕ) (test : StatisticalTest ((Fin n → ℝ) × ℝ) T),
            VectorGuarantee test k ε → (2 : ℝ) ^ (c * k) ≤ T := by sorry

end MatrixSenseRank.Testing.Supplement
