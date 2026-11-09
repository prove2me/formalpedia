-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_14
-- name    : L22EigEst.lemma_4_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:21:07.008633+00:00
-- url     : https://prove2.me/theorems/2ac3fade-c340-4639-b9c1-d20af34027d3
-- title:
--   Lemma 4.14 — $\lambda_{\max}(SAS^\top)\le\lambda_{\max}(A)+160L$
-- statement:
--   Let $L>0$, $n\ge1$, and let $A\in\mathbb R^{n\times n}$ be symmetric with every non-zero eigenvalue at least $L$ (so $A$ is positive semidefinite). Let $S$ be a diagonal matrix satisfying the subspace embedding condition for $A$ (Definition 4.12). Then
--
--   $$\lambda_{\max}(SAS^\top)\le\lambda_{\max}(A)+160L .$$
--
--   The new $O(L)$ bound replaces the $L\log(\lambda_{\max}(A)/L)$ of [SW25, Lemma 5.6]. That saving removes a $\log^2(1/\varepsilon)$ factor from the sample size.
--
--   Differences from the source:
--   - generalization: S a sampling matrix (δ_i/√p_i on the diagonal) → S = diag(d) for any real vector d; reason: the proof uses only the subspace embedding condition, never the form of the diagonal; every sampling matrix in the n × n view is diag(d)
--   - encoding: L, the parameter of Definition 4.12 → an arbitrary L > 0; reason: the distortion min(L/λ, 1/10) presupposes L > 0
--   - encoding: λmax of an n × n matrix → gamma _ _ 0, with n ≥ 1; reason: λmax is undefined for n = 0
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.14, p.20

import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_SECond
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.14** (p.20), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "For any symmetric matrix A ∈ ℝ^{n×n} whose non-zero eigenvalues are all at least
L, if S satisfies the subspace embedding condition for A, then λmax(SAS⊺) ≤ λmax(A) + 160L."

**Formalization Note.** "All at least L" is signed (so `A` is positive semidefinite, as the proof
notes). `λmax = gamma _ _ 0`, which needs `n ≥ 1`. Stated for every `L > 0` and every real
diagonal `S = diag(d)`. -/
theorem lemma_4_14 (n : ℕ) (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (L : ℝ) (hL : 0 < L) (hspec : ∀ i, gamma A hA i ≠ 0 → L ≤ gamma A hA i) (d : Fin n → ℝ)
    (hS : SECond A (Matrix.diagonal d) L) :
    gamma (Matrix.diagonal d * A * Matrix.diagonal d) (isHermitian_diag_conj d hA) ⟨0, hn⟩ ≤
      gamma A hA ⟨0, hn⟩ + 160 * L := by sorry

end L22EigEst
