-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_7
-- name    : OptimalTraceDistance.Estimation.proposition_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:43:38.08808+00:00
-- url     : https://prove2.me/theorems/2a17463a-65bf-4241-933f-f34a65a8a639
-- title:
--   Proposition 2.7 — unbiased polynomial estimator
-- statement:
--   Let $f$ be a known trace expression on $d\times d$ matrices, real on Hermitian inputs, and $n\ge\deg f$, $n\ge1$. There is a measurement chosen from $f,n$ before the unknown states, using at most $n$ copies of each input, whose real outcome is the spectral outcome of $G_{f,n}$ on the labelled state $\tau^{\otimes n}$. For every density pair,
--   $$\mathbb E\widehat f_n=f(S_+,S_-).$$
--   The observable is Hermitian and the outcome is integrable. The physical realization uses the actual tensor input rather than a state-dependent invented classical law.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: The output of Algorithm 1 using at most n copies of each input → A normalized POVM on n copies of each state realizes its finite spectral law, with integrability; reason: The independent labels can ignore unused input copies, and finite spectral support gives the same real expectation
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 2.7, p. 10.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_2_7 (d n : ℕ) (hd : 0 < d) (hn : 0 < n)
    (g : TraceExpression d) (hg : realOnHermitian g) (hdegree : expressionDegree g ≤ n) :
  (observable g n).IsHermitian ∧ inputCost n = n ∧
  ∃ M : TwoStateMeasurement d n, ∀ (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ),
    let μ := spectralLaw (observable g n) (powerState (labelledState ρ σ) n)
    outcomeLaw M ρ σ hρ hσ = μ ∧ Integrable (fun x : ℝ => x) μ ∧
      (∫ x : ℝ, x ∂μ) = (evaluate g (plus ρ σ) (minus ρ σ)).re := by sorry

end OptimalTraceDistance.Estimation
