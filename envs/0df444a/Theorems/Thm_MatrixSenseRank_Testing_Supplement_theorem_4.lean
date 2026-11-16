-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_Supplement_theorem_4
-- name    : MatrixSenseRank.Testing.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:14:07.581843+00:00
-- url     : https://prove2.me/theorems/72297bb1-4ab1-4806-b3ff-ba6bedb9f19c
-- title:
--   Theorem 4 — exponential lower bound for rank-one measurements
-- statement:
--   There are absolute $c>0$, an integer $k_0\ge4$, and a dimension threshold $N(k)$ depending only on $k$ such that the following holds for every $k\ge k_0$, every $n\ge\max\{k+1,N(k)\}$, and every $0<\varepsilon\le k^{-3/2}$. A randomized test observes full pairs
--
--   $$ (X,\langle A,X\rangle_F+\eta),\qquad X=gg'^\top,\quad g,g'\sim N(0,I_n),\quad\eta\sim N(0,1), $$
--
--   with all draws independent across samples. If for every unknown real unit-Frobenius matrix $A$ it accepts with probability at least $9/10$ at rank at most $k$ and rejects with probability at least $9/10$ at normalized rank distance at least $\varepsilon$, then its sample count satisfies
--
--   $$ T\ge\exp(ck). $$
--
--   Targets are arbitrary real matrices, without a diagonal, symmetry or positivity restriction. The threshold is inclusive and the test sees the entire observation matrix.
--
--   This gives the exponential dependence on rank that complements the existing goal. The proof's final sentence on printed p.30 supplies the full accuracy range, including the displayed $\Theta(k^{-3/2})$ scale.
--
--   Differences from the source:
--   - encoding: finite real Euclidean matrices with the paper's Frobenius norm → matrices indexed by Fin n and Fin m, with the published Frobenius and normalized-distance definitions; reason: a change of coordinates and indexing only; positive dimensions are retained
--   - encoding: possibly randomized algorithms observing full sample pairs → measurable Boolean probability kernels averaged under the actual independent sample law; reason: this represents all internal randomization without removing observed covariates
--   - encoding: absolute asymptotic constants and sufficiently large dimensions → existential constants and thresholds preceding every dimension, accuracy, sample count and test; reason: the constants are uniform; no numerical coefficient is invented
--   - encoding: displayed accuracy Theta(k^(-3/2)) and the proof's final conclusion for every 0<epsilon<=k^(-3/2) → the entire explicitly proved interval 0<epsilon<=1/(k sqrt(k)); reason: this retains the proof's full range rather than assigning an arbitrary implicit Theta coefficient
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, Matrix sensing meets property testing: Sample-optimal testing for low rank, STOC 2027 submission #380 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf, PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b; Theorem 4, printed p. 28, PDF p. 29 (1-based).

import Definitions.Def_MatrixSenseRank_Testing_Supplement_Experiments

set_option autoImplicit false
open ProbabilityTheory

namespace MatrixSenseRank.Testing.Supplement

/-- Theorem 4, printed p.28 / PDF p.29; its proof (p.30 / PDF p.31) supplies the full accuracy range. -/
theorem theorem_4 :
    ∃ c : ℝ, 0 < c ∧ ∃ (k₀ : ℕ) (N : ℕ → ℕ), 4 ≤ k₀ ∧
      ∀ k n : ℕ, k₀ ≤ k → max (k + 1) (N k) ≤ n →
        ∀ ε : ℝ, 0 < ε → ε ≤ accuracyScale k →
          ∀ (T : ℕ) (test : StatisticalTest (Observation n n) T),
            RankGuarantee test (observationLaw (gaussianReal 0 1)) k ε ((9 : ℝ) / 10) →
              Real.exp (c * k) ≤ T := by sorry

end MatrixSenseRank.Testing.Supplement
