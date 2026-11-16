-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_theorem_1
-- name    : MatrixSenseRank.Testing.Supplement.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:11:45.04777+00:00
-- url     : https://prove2.me/theorems/a46338c4-f769-46db-8b5a-2b068c1acdc7
-- title:
--   Theorem 1 — full-Gaussian linear sample lower bound
-- statement:
--   There are absolute $c>0$ and an integer $n_0\ge2$ such that the following holds for every $n\ge n_0$. Fix any randomized test using $T$ entire noiseless observations $(X,\langle A,X\rangle_F)$, where $X$ has independent standard normal entries. Suppose that for every unknown symmetric positive semidefinite matrix $A$ with $\|A\|_F=1$, the test accepts with probability at least $9/10$ when $\operatorname{rank}(A)\le1$ and rejects with probability at least $9/10$ when $\operatorname{dist}_1(A)\ge\sqrt{2-\sqrt2}$. Then
--
--   $$T\ge cn.$$
--
--   The test is fixed before the target, and the soundness threshold is inclusive. The positive semidefinite promise gives the stronger lower bound; any tester for unrestricted real matrices also satisfies this premise. The normalized distance uses unit-Frobenius rank-at-most-one approximants.
--
--   This is the full-observation impossibility result complementary to the noisy recovery-based upper bound.
--
--   Differences from the source:
--   - encoding: finite real Euclidean matrices with the paper's Frobenius norm → matrices indexed by Fin n and Fin m, with the published Frobenius and normalized-distance definitions; reason: a change of coordinates and indexing only; positive dimensions are retained
--   - encoding: possibly randomized algorithms observing full sample pairs → measurable Boolean probability kernels averaged under the actual independent sample law; reason: this represents all internal randomization without removing observed covariates
--   - encoding: absolute asymptotic constants and sufficiently large dimensions → existential constants and thresholds preceding every dimension, accuracy, sample count and test; reason: the constants are uniform; no numerical coefficient is invented
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Theorem 1, printed p. 13, PDF p. 14 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments

set_option autoImplicit false

namespace MatrixSenseRank.Testing.Supplement

/-- Theorem 1, printed p.13 / PDF p.14, including the PSD promise. -/
theorem theorem_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, 2 ≤ n₀ ∧
      ∀ n T : ℕ, n₀ ≤ n →
        ∀ test : StatisticalTest (Observation n n) T,
          RankGuarantee test (fullObservationLaw 0) 1
            (Real.sqrt (2 - Real.sqrt 2)) ((9 : ℝ) / 10)
            (fun A => A.PosSemidef) → c * n ≤ T := by sorry

end MatrixSenseRank.Testing.Supplement
