-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_13
-- name    : L22EigEst.lemma_4_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:19:55.851448+00:00
-- url     : https://prove2.me/theorems/27093ef4-85e0-40f2-a462-695ee900378c
-- title:
--   Lemma 4.13 — lower bound $\lambda_i(SAS^\top)\ge\lambda_i(A)-51L$ for positive eigenvalues
-- statement:
--   Let $L>0$ and let $A\in\mathbb R^{n\times n}$ be symmetric with every non-zero eigenvalue of magnitude at least $L$. Let $S$ be a diagonal matrix satisfying the subspace embedding condition for $A$ (Definition 4.12): for every $\lambda\ge L$, $S$ is a $\min(L/\lambda,1/10)$-distortion subspace embedding of the span of the eigenvectors of $A$ with eigenvalue of magnitude at least $\lambda$. Then for every $i$ with $\lambda_i(A)>0$,
--
--   $$\lambda_i(SAS^\top)\ge\lambda_i(A)-51L .$$
--
--   This is Lemma 5.5 of [SW25], quoted by the paper; it gives the lower half of Lemma 4.6.
--
--   Differences from the source:
--   - generalization: S a sampling matrix (δ_i/√p_i on the diagonal) → S = diag(d) for any real vector d; reason: the proof uses only the subspace embedding condition, never the form of the diagonal; every sampling matrix in the n × n view is diag(d)
--   - encoding: L, the parameter of Definition 4.12 → an arbitrary L > 0; reason: the distortion min(L/λ, 1/10) presupposes L > 0; §4.4's lemmas are stated for a generic L
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.13, p.19

import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_SECond
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.13** (Lemma 5.5 in [SW25], p.19), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "For any symmetric matrix A ∈ ℝ^{n×n} with all non-zero
eigenvalues of magnitude at least L, if S satisfies the subspace embedding condition for A, then we
have that for all i where λi(A) > 0, λi(SAS⊺) ≥ λi(A) − 51L."

**Formalization Note.** Stated for every `L > 0` and every real diagonal `S = diag(d)` (the `n × n`
view of a sampling matrix). The subspace embedding condition is `SECond A S L` (Definition 4.12). -/
theorem lemma_4_13 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (L : ℝ)
    (hL : 0 < L) (hspec : ∀ i, gamma A hA i ≠ 0 → L ≤ |gamma A hA i|) (d : Fin n → ℝ)
    (hS : SECond A (Matrix.diagonal d) L) :
    ∀ i, 0 < gamma A hA i →
      gamma A hA i - 51 * L ≤
        gamma (Matrix.diagonal d * A * Matrix.diagonal d) (isHermitian_diag_conj d hA) i := by sorry

end L22EigEst
