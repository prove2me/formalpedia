-- Prove2me | Theorems.Thm_LostSalesConstantOrder_LargeLeadTime_theorem_11
-- name    : LostSalesConstantOrder.LargeLeadTime.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T18:03:12.564144+00:00
-- url     : https://prove2.me/theorems/c1892f3c-41c4-4963-bc8a-91b02a12f5e3
-- title:
--   Theorem 11: Lipschitz CLT rate $3n^{-1/2}\mathbb E|X_1|^3$
-- statement:
--   Let $F:\mathbb R\to\mathbb R$ be Lipschitz with constant at most $1$, i.e. $|F(x)-F(y)|\le|x-y|$ for all $x,y$. Let $X_1,X_2,\dots$ be i.i.d. real random variables with $\mathbb E[X_1]=0$, $\mathbb E[X_1^2]=1$ and $\mathbb E[|X_1|^3]<\infty$, and let $N$ be a standard normal random variable. Then for all $n\ge1$,
--   $$
--   \Big|\mathbb E\Big[F\Big(n^{-1/2}\sum_{i=1}^nX_i\Big)\Big]-\mathbb E[F(N)]\Big|\ \le\ 3n^{-1/2}\,\mathbb E[|X_1|^3].
--   $$
--
--   This explicit rate in the central limit theorem (Chen and Shao, Stein's method) drives the proof of Lemma 10.
--
--   **Formalization Note** The sequence is indexed from $0$: $X_0,\dots,X_{n-1}$ are the paper's $X_1,\dots,X_n$. Independence is `iIndepFun` and identical distribution is `IdentDistrib` with $X_0$; $\mathbb E[F(N)]$ is the integral of $F$ against `gaussianReal 0 1`.
-- source:
--   Goldberg, Katz-Rogozhnikov, Lu, Sharma & Squillante, Asymptotic Optimality of Constant-Order Policies for Lost Sales Inventory Models with Large Lead Times, arXiv:1211.4063v2, p. 12, Theorem 11 (citing Chen & Shao 2005)

import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace LostSalesConstantOrder.LargeLeadTime

/-- Theorem 11, p. 12 ([5], Chen & Shao 2005): if `F : ℝ → ℝ` is `1`-Lipschitz and `X_1, X_2, …`
are i.i.d. with `E[X_1] = 0`, `E[X_1²] = 1` and `E[|X_1|³] < ∞`, then for all `n ≥ 1`,
`|E[F(n^{-1/2} Σ_{i=1}^n X_i)] − E[F(N)]| ≤ 3 n^{-1/2} E[|X_1|³]`, with `N` standard normal.
(`X 0, …, X (n − 1)` are the paper's `X_1, …, X_n`.) -/
theorem theorem_11 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hid : ∀ i, IdentDistrib (X i) (X 0) μ μ)
    (h3 : Integrable (fun ω => |X 0 ω| ^ 3) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0) (hvar : ∫ ω, X 0 ω ^ 2 ∂μ = 1)
    (F : ℝ → ℝ) (hF : LipschitzWith 1 F) (n : ℕ) (hn : 1 ≤ n) :
    |∫ ω, F ((n : ℝ) ^ (-(1 / 2 : ℝ)) * ∑ i ∈ Finset.range n, X i ω) ∂μ -
        ∫ y, F y ∂(gaussianReal 0 1)| ≤
      3 * (n : ℝ) ^ (-(1 / 2 : ℝ)) * ∫ ω, |X 0 ω| ^ 3 ∂μ := by sorry

end LostSalesConstantOrder.LargeLeadTime
