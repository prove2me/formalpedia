-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_4_3
-- name    : OptimalTraceDistance.Estimation.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:43:45.618792+00:00
-- url     : https://prove2.me/theorems/2af59a8c-9d95-4ed9-bc4a-12ae38f353d5
-- title:
--   Proposition 4.3 — variance from Taylor coefficients
-- statement:
--   Let $\rho,\sigma$ be densities, $Q$ an orthogonal projector and $\beta>0$ with $\|QS_+Q\|_\infty\le\beta$. Let $f$ be a known trace expression real on Hermitian inputs, $D=\deg f$. Suppose each order-$j$ Taylor coefficient at $(QS_+Q,QS_-Q)$ has an $M_j$-bounded ordered representation, valid for all complex perturbations. For every $n\ge D$, $n\ge1$,
--   $$\operatorname{Var}G_{f,Q,n}\le\sum_{j=1}^D\binom nj^{-1}M_j^2\frac{\prod_{\ell=0}^{j-1}(1+\ell\beta)}{(j-1)!}.$$
--   The variance is taken in the original normalized labelled product state. The compressed pair is never normalized.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 4.3, p. 16.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_4_3 (d : ℕ) (hd : 0 < d)
    (ρ σ : Mat d) (hρ : Density ρ) (hσ : Density σ)
    (Q : Mat d) (hQ : projector Q) (β : ℝ) (hβ : 0 < β)
    (hbound : opNorm (compress Q (plus ρ σ)) ≤ β)
    (g : TraceExpression d) (hg : realOnHermitian g) (M : ℕ → ℝ)
    (hM : ∀ j ∈ Finset.Icc 1 (expressionDegree g),
      HasOrderedBound j (taylor g (compress Q (plus ρ σ)) (compress Q (minus ρ σ)) j) (M j))
    (n : ℕ) (hn : 0 < n) (hdegree : expressionDegree g ≤ n) :
  polynomialVariance (substituteCompression Q g) n ρ σ ≤
    ∑ j ∈ Finset.Icc 1 (expressionDegree g),
      (Nat.choose n j : ℝ)⁻¹ * (M j)^2 * cycleFactor β j := by sorry

end OptimalTraceDistance.Estimation
