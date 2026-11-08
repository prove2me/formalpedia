-- Prove2me | Theorems.Thm_LowDimMeanEst_lemma_43
-- name    : LowDimMeanEst.lemma_43
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:53:38.160972+00:00
-- url     : https://prove2.me/theorems/934a2be2-b5ee-4d00-9b05-a3be1053ae19
-- title:
--   Lemma 43 — if $\mathrm{Tr}(A)\ge R$ then the trimmed empirical variance in every unit direction is $\le\frac{1}{3nR}\log\frac1\delta$
-- statement:
--   **Lemma 43.** Let $\delta\in(0,1)$, let $x_1,\dots,x_n\in\mathbb R^d$, and let $A$ be a trimming matrix for these samples and $\delta$ (Definition `TrimmingMatrix`). For every $R>0$, if $\mathrm{Tr}(A)\ge R$ then for every unit vector $v$,
--
--   $$\frac1n\sum_i\big(1-\min(1,x_i^\top Ax_i)\big)(x_i\cdot v)^2\ \le\ \frac{1}{3nR}\log\frac1\delta .$$
--
--   A large trimming matrix forces a small trimmed variance; with Lemma 44 this bounds the parameter $\alpha$ of Algorithm 2.
--
--   Differences from the source:
--   - generalization: the trimming matrix A computed by Algorithm 2 (Lemma 3) → every A with IsTrimmingMatrix: A ⪰ 0, Σ min(1, x_i^⊤Ax_i) = (1/3)log(1/δ), Lemma 3's maximality; reason: the computed matrix has these properties (Lemma 3 and the weight sum of Algorithm 2), so the statement specializes to it; A is not unique (p.9)
-- source:
--   Lee, Mathashery, Valiant, Wang, Optimal Sub-Gaussian Mean Estimation in Low Dimensions, STOC 2027 submission (manuscript sha256 7316d30e…), Lemma 43, p.83

import Mathlib
import Definitions.Def_LowDimMeanEst_TrimmingMatrix

namespace LowDimMeanEst

/-- **Lemma 43**, p.83.

Lee, Mathashery, Valiant, Wang, *Optimal Sub-Gaussian Mean Estimation in Low Dimensions*, STOC 2027
submission (manuscript sha256 7316d30e…).

"Suppose the probability parameter δ ∈ (0, 1). Consider samples x₁, …, xₙ ∈ ℝᵈ. Consider the
trimming matrix A implicitly computed by Algorithm 2 (Lemma 3) with input {xᵢ} and parameter δ. For
any R > 0, if Tr(A) ≥ R, the trimmed empirical variance in any unit direction v can be bounded above
as (1/n) Σᵢ (1 − min(1, xᵢ⊤Axᵢ))(xᵢ · v)² ≤ (1/(3nR)) log(1/δ)."

**Formalization Note.** "The trimming matrix A implicitly computed by Algorithm 2" is any `A` with
`IsTrimmingMatrix x δ A` (PSD, weight sum `(1/3) log(1/δ)`, Lemma 3's maximality condition).
-/
theorem lemma_43 {d n : ℕ} (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (x : Fin n → E d)
    (A : E d →L[ℝ] E d) (hA : IsTrimmingMatrix x δ A) (R : ℝ) (hR : 0 < R) (htr : R ≤ tr A)
    (v : E d) (hv : ‖v‖ = 1) :
    (1 / (n : ℝ)) * trimmedQuad x A v ≤ logInv δ / (3 * n * R) := by sorry

end LowDimMeanEst
