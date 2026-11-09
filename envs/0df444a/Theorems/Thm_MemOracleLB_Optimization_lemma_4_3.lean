-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_4_3
-- name    : MemOracleLB.Optimization.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:32.062201+00:00
-- url     : https://prove2.me/theorems/c3ef19aa-1d2d-48f9-aade-ccfaeb520b48
-- title:
--   Lemma 4.3 — Separating query
-- statement:
--   There are absolute constants $\ell>3$, $c_0>0$ and a dimension threshold such that the following holds for every sufficiently large $n$. Put $L=\ell n$, let $R$ have independent $N(0,1/n)$ entries, and consider any randomized membership-query algorithm with $R_n$ revealed. Couple its runs on the hard pair with the same seed, and let $\tau$ be the one-based index of its first separating query, or $\infty$ when no such query occurs. Then
--
--   $$t_n=\left\lfloor c_0\frac{n^2}{\log^2 n}\right\rfloor,\qquad\Pr(\tau\le t_n)<\frac14.$$
--
--   The probability is over the original unconditioned matrix law and the independent algorithm seed. The action is jointly measurable in the public row and seed for each finite answer history. The oracle gives ordinary Boolean membership responses; the enhanced oracle is not an assumption of this statement.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - encoding: n-1 rows in n dimensions → m rows in dimension m+1; reason: renaming n=m+1 avoids truncated natural subtraction and changes no positive-dimensional instance
--   - encoding: the standing sufficiently large absolute ambient dimension on PDF p.8 → an existential natural threshold N at least 2 before the dimension and all instance data; reason: this makes the source asymptotic quantifier explicit and keeps logarithms and denominators in their stated domains
--   - reading: a universal c0 after the phrase for any algorithm, and the fixed universal multiple L chosen at the start of §4.1 → ell and c0 quantified before the dimension and every algorithm, with L=ell*n; reason: universal constants and the fixed hard pair cannot depend on the algorithm
--   - encoding: probability jointly over the revealed Gaussian row, hidden rows and internal randomness → a product probability law and an action jointly measurable in the public row and seed; reason: joint measurability gives exactly the probability in this lemma and is not imposed on the goal algorithm
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 4.3, PDF p. 20 (printed p. 19), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_OracleModel

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
universe u43

namespace MemOracleLB.Optimization

/-- Lemma 4.3, PDF p.20 (printed p.19). The floor is visible on the PDF page;
the text layer omits it. The probability is unconditioned and includes the seed. -/
theorem lemma_4_3 : ∃ ℓ c₀ : ℝ, 3 < ℓ ∧ 0 < c₀ ∧ ∃ N : ℕ, 2 ≤ N ∧
    ∀ m : ℕ, N ≤ m + 1 → ∀ {Ω : Type u43} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (A : RevealedAlgorithm (m + 1) Ω),
      ((matrixLaw (m + 1)).prod P)
        {p | separatingIndex A (ℓ * (m + 1)) p.1 p.2 ≤
          (⌊c₀ * (m + 1 : ℝ) ^ 2 / (Real.log (m + 1)) ^ 2⌋₊ : ℕ∞)} < 1 / 4 := by sorry

end MemOracleLB.Optimization
