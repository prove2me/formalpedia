-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_15
-- name    : L22EigEst.lemma_4_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:04.164107+00:00
-- url     : https://prove2.me/theorems/bc529ea1-6cae-4152-a3de-daaf0604ffc1
-- title:
--   Lemma 4.15 — upper bound $\lambda_i(SAS^\top)\le\lambda_i(A)+160L$ for positive eigenvalues
-- statement:
--   Let $L>0$ and let $A\in\mathbb R^{n\times n}$ be symmetric with every non-zero eigenvalue of magnitude at least $L$. Let $S$ be a diagonal matrix satisfying the subspace embedding condition for $A$ (Definition 4.12). Then for every $i$ with $\lambda_i(A)>0$,
--
--   $$\lambda_i(SAS^\top)\le\lambda_i(A)+160L .$$
--
--   Together with Lemma 4.13, applied to $A'_H$ and $-A'_H$, it gives Lemma 4.6.
--
--   Differences from the source:
--   - generalization: S a sampling matrix (δ_i/√p_i on the diagonal) → S = diag(d) for any real vector d; reason: the proof uses only the subspace embedding condition, never the form of the diagonal; every sampling matrix in the n × n view is diag(d)
--   - encoding: L, the parameter of Definition 4.12 → an arbitrary L > 0; reason: the distortion min(L/λ, 1/10) presupposes L > 0
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.15, p.21

import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_SECond
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.15** (p.21), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "For any symmetric matrix A ∈ ℝ^{n×n} with all non-zero eigenvalues of magnitude
at least L, if S satisfies the subspace embedding condition for A, then we have that for all i
where λi(A) > 0, λi(SAS⊺) ≤ λi(A) + 160L"

**Formalization Note.** Stated for every `L > 0` and every real diagonal `S = diag(d)`. -/
theorem lemma_4_15 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (L : ℝ)
    (hL : 0 < L) (hspec : ∀ i, gamma A hA i ≠ 0 → L ≤ |gamma A hA i|) (d : Fin n → ℝ)
    (hS : SECond A (Matrix.diagonal d) L) :
    ∀ i, 0 < gamma A hA i →
      gamma (Matrix.diagonal d * A * Matrix.diagonal d) (isHermitian_diag_conj d hA) i ≤
        gamma A hA i + 160 * L := by sorry

end L22EigEst
