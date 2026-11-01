-- Prove2me | Theorems.Thm_OLPDual_lemma_5
-- name    : OLPDual.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:21:35.824512+00:00
-- url     : https://prove2.me/theorems/639c75ff-0e71-468a-bfbd-edadaa763472
-- title:
--   Lemma 5 (Matrix Hoeffding), p.34 (corrected: $2d\exp(-nt^2/(2B^2))$)
-- statement:
--   Let $X_1,\dots,X_n\in\mathbb R^d$ be i.i.d. random vectors with $\mathbb E(X_kX_k^\top)=M$ and $\|X_k\|^2\le B$ almost surely, and let $Z=\frac1n\sum_{k=1}^nX_kX_k^\top$. Then for all $t>0$,
--
--   $$
--   \mathbb P\bigl(\|M-Z\|_S\ge t\bigr)\le 2d\exp\Bigl(-\frac{nt^2}{2B^2}\Bigr),
--   $$
--
--   where $\|\cdot\|_S$ is the spectral norm. This inequality controls the empirical second-moment matrix of the columns in Step 1 of the proof of Proposition 4.
--
--   **Formalization Note** The spectral norm is the $\ell^2$ operator norm of `Matrix.Norms.L2Operator`. The identity $\mathbb E(X_kX_k^\top)=M$ is stated entry by entry.
--
--   Differences from the source:
--   - correction: ℙ(‖M − Z‖_S ≥ t) ≤ d · exp(−t²/(Bn)) → ℙ(‖M − Z‖_S ≥ t) ≤ 2d · exp(−nt²/(2B²)); reason: the printed bound is false: n = 1, d = 1, X = 10 with probability 0.01 and 0 otherwise has B = 100, M = 1 and ℙ(|M − Z| ≥ 99) = 0.01 > exp(−98.01); the corrected bound is the cited Corollary 4.2 for (X_kX_kᵀ − M)/n with both tails
--   - encoding: i.i.d. random vectors in ℝ^d, d and n positive → Measurable, iIndepFun and pairwise IdentDistrib, 0 < d, 0 < n; reason: the usual meaning of the words
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Lemma 5, p.34, corrected from Mackey, Jordan, Chen, Farrell, Tropp, Ann. Probab. 42 (2014), Corollary 4.2

import Mathlib
import Definitions.Def_OLPDual_Model

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open scoped Matrix.Norms.L2Operator

namespace OLPDual

/-- **Lemma 5 (Matrix Hoeffding's Inequality), corrected**, Li–Ye, arXiv:1909.05499v5, p.34 (PDF 34):
for i.i.d. random vectors `X_1, …, X_n ∈ ℝ^d` with `E(X_k X_kᵀ) = M`, `‖X_k‖² ≤ B` almost surely and
`Z = (1/n) Σ_k X_k X_kᵀ`, one has `ℙ(‖M − Z‖_S ≥ t) ≤ 2d exp(−n t²/(2B²))` for all `t > 0`.
**Formalization Note** The printed bound `d exp(−t²/(Bn))` is false; the bound here is Corollary 4.2
of Mackey et al. (2014), the paper's own citation, applied to `(X_k X_kᵀ − M)/n`. `‖·‖_S` is the
`ℓ²` operator norm of `Matrix.Norms.L2Operator`. `E(X_k X_kᵀ) = M` is stated entry by entry. -/
theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n) (X : Fin n → Ω → E d) (hmeas : ∀ k, Measurable (X k))
    (hindep : iIndepFun X μ) (hident : ∀ k l, IdentDistrib (X k) (X l) μ μ)
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : ∀ k i j, ∫ ω, X k ω i * X k ω j ∂μ = M i j)
    {B : ℝ} (hB : ∀ k, ∀ᵐ ω ∂μ, ‖X k ω‖ ^ 2 ≤ B) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t ≤ ‖M - (1 / (n : ℝ)) • ∑ k, Matrix.vecMulVec (⇑(X k ω)) (⇑(X k ω))‖} ≤
      2 * (d : ℝ) * Real.exp (-((n : ℝ) * t ^ 2) / (2 * B ^ 2)) := by sorry

end OLPDual
