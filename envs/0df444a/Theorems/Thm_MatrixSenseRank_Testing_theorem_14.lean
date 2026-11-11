-- Prove2me | Theorems.Thm_MatrixSenseRank_Testing_theorem_14
-- name    : MatrixSenseRank.Testing.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:48:05.937931+00:00
-- url     : https://prove2.me/theorems/e15a3035-57f9-4557-8b75-99c0a976f6bf
-- title:
--   Theorem 14 — label-only noisy sparsity testing
-- statement:
--   There are absolute constants $a>0$ and an integer $d\ge1$ with the following property. Let $k\ge0$ be a sparsity parameter, and let $D,\eta$ be Borel probability laws on $\mathbb R$ with finite moments through order $4k+4$. The input law has mean zero, variance one, and
--   $$\tau=\min_{1\le j\le k+1}|\kappa_{2j}(D)|>0.$$
--   For $C\ge1$ and $\varepsilon>0$, there is a finite-sample measurable Boolean test, chosen before the dimension and unknown vector, using
--   $$T\le\left\lceil a\left(1+k!+m_{4k+4}(D)+m_{4k+4}(\eta)+(C/\varepsilon)^k+\tau^{-1}\right)^d\right\rceil.$$
--   For every positive dimension $n$ and every vector $w\in\mathbb R^n$ promised to satisfy $1/C\le\|w\|_2\le C$, its observations are only the independent noisy labels $y=w\cdot x+e$, where $x\sim D^{\otimes n}$ and $e\sim\eta$ are independent. It accepts every $k$-sparse vector with probability at least $9/10$ and rejects every vector with $\operatorname{dist}(w,k\text{-sparse})\ge\varepsilon$ with probability at least $9/10$.
--
--   The relative distance minimizes $\|w-v\|_2/\|w\|_2$ over all $k$-sparse $v$, without a norm constraint. This is the general result attributed to Chen, De and Servedio in the pinned submission, including its label-only input restriction. No MGF, centering, symmetry, boundedness or Gaussian condition is imposed on the noise.
--
--   Differences from the source:
--   - encoding: finite even moments and the displayed polynomial sample dependence → integrable powers through 4k+4 for both laws, and absolute a,d bounding a ceiling of a power of one plus the displayed arguments; reason: finite top even absolute moment implies every lower moment; the D moment is needed for its displayed finite bound, and positive ε and C≥1 make the norm promise and ratios well-defined
--   - encoding: an algorithm using independent noisy labels with success probability at least 9/10 → a measurable Boolean Markov kernel fixed before dimension and hidden vector, with acceptance at least 9/10 in the yes-case and at most 1/10 at relative distance ≥ε; reason: kernel composition and product observation laws include all sampling and private randomness, and the complementary acceptance inequality is the exact rejection guarantee
-- source:
--   Yiqiao Bao, Anindya De, Shivam Nadimpalli, Rocco A. Servedio, Chenyang Sun, Nathan White, STOC 2027 submission #380 (October 2026), §6, Theorem 14 (Theorem 7.1 of [CDS20]), Eq. (22) and both explanatory bullets, printed pp. 26–27 / PDF pp. 27–28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/380.pdf; PDF SHA-256 6e4e46ced4dfe65bbe94e4cec3e8230032914efef9d87b0f544bbea151a00c3b.

import Mathlib
import Definitions.Def_MatrixSenseRank_Testing_Experiment

set_option autoImplicit false
open MeasureTheory

namespace MatrixSenseRank.Testing

/-- Theorem 14, printed pp.26–27 / PDF pp.27–28: all finite-moment input laws,
not just product-normal or laws with a finite MGF. Test and sample count precede n,w. -/
theorem theorem_14 :
    ∃ a : ℝ, 0 < a ∧ ∃ d : ℕ, 1 ≤ d ∧
    ∀ (k : ℕ) (D η : Measure ℝ),
      IsProbabilityMeasure D → IsProbabilityMeasure η →
      FiniteMoments D (4 * k + 4) → FiniteMoments η (4 * k + 4) →
      rawMoment D 1 = 0 → rawMoment D 2 = 1 → 0 < cumulantFloor D k →
      ∀ (C ε : ℝ), 1 ≤ C → 0 < ε →
      ∃ (T : ℕ) (test : StatisticalTest ℝ T),
        T ≤ polynomialBound a d [(k.factorial : ℝ), rawMoment D (4 * k + 4),
          rawMoment η (4 * k + 4), (C / ε) ^ k, (cumulantFloor D k)⁻¹] ∧
        SparsityGuarantee test D η k ε C := by sorry

end MatrixSenseRank.Testing
