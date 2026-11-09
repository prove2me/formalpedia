-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_4_4
-- name    : OptimalTraceDistance.Estimation.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:38.359253+00:00
-- url     : https://prove2.me/theorems/7ac6a088-67ec-4a82-a464-67e2d7361d5e
-- title:
--   Lemma 4.4 — both univariate variance bounds
-- statement:
--   There is a universal $C>0$ such that for every density pair, orthogonal projector $Q$, $K\ge2$ and $n\ge2K$, the observable for $\operatorname{tr}q_K(QYQ)$ satisfies
--   $$\operatorname{Var}G_{K,Q,n}\le K^{-2}\big(\exp(CK^2/n)-1\big).$$
--   Moreover, whenever $\beta>0$ and $\|QS_+Q\|_\infty\le\beta$,
--   $$\operatorname{Var}G_{K,Q,n}\le\frac1n+K^{-2}\left[\exp(CK/\sqrt n)+\exp(C\beta K^2/n)\right].$$
--   Both estimates use a common universal constant and the same actual observable on the fresh batch.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma 4.4, p. 17; continued p.18.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_4_4 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 0 < d →
  ∀ ρ σ : Mat d, Density ρ → Density σ → ∀ Q : Mat d, projector Q →
  ∀ K n : ℕ, 2 ≤ K → 2*K ≤ n →
    polynomialVariance (substituteCompression Q (univariate d K)) n ρ σ ≤
      (Real.exp (C*(K : ℝ)^2/n)-1)/(K : ℝ)^2 ∧
    ∀ β : ℝ, 0 < β → opNorm (compress Q (plus ρ σ)) ≤ β →
      polynomialVariance (substituteCompression Q (univariate d K)) n ρ σ ≤
        1/(n : ℝ) + (Real.exp (C*K/Real.sqrt n) +
          Real.exp (C*β*(K : ℝ)^2/n))/(K : ℝ)^2 := by sorry

end OptimalTraceDistance.Estimation
