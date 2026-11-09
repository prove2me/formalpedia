-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_6
-- name    : L22EigEst.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:23:43.447203+00:00
-- url     : https://prove2.me/theorems/a66245a0-bcd2-442b-b525-6bf1b28d0d8d
-- title:
--   Lemma 4.6 — under E1, $|\lambda_i(SA'_HS^\top)-\lambda_i(A'_H)|\le160L$
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric, $\varepsilon>0$, $L=\varepsilon\|A\|_F/200$, $A'$ the matrix of (2) and $A'_H$ the part of $A'$ with eigenvalues of magnitude at least $L$ (Definition 2.3). Let $S$ be a diagonal matrix satisfying event E1: for every $\lambda\ge L$, $S$ is a $\min(L/\lambda,1/10)$-distortion subspace embedding of the span of the eigenvectors of $A'$ with eigenvalue of magnitude at least $\lambda$. Then for all $i\in[n]$,
--
--   $$|\lambda_i(SA'_HS^\top)-\lambda_i(A'_H)|\le160L ,$$
--
--   where the spectrum of $SA'_HS^\top$ is padded with zeros to length $n$ and sorted.
--
--   Since $160L\le\varepsilon\|A\|_F$, the sampled large part of $A'$ reproduces the spectrum of $A'_H$. This improves the $O(L\log(\lambda_{\max}/L))$ bound of [SW25, Theorem 5.8].
--
--   Differences from the source:
--   - generalization: S a sampling matrix (δ_i/√p_i on the diagonal) → S = diag(d) for any real vector d; reason: the proof uses only the subspace embedding condition, never the form of the diagonal; every sampling matrix in the n × n view is diag(d)
--   - generalization: the setting of Definition 4.2, ε ∈ (0, 1) → every ε > 0; reason: the lemma is deterministic and its proof (Lemmas 4.13, 4.15) uses only L > 0 or A = 0
--   - encoding: spectrum of SA′_H S⊺ (s × s) padded with n − s zeros and sorted → the sorted n eigenvalues of the n × n matrix S A′_H S; reason: the n × n view of S (p.9) gives exactly the padded spectrum
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.6, p.14

import Definitions.Def_L22EigEst_rowSq
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_L22EigEst_highPart
import Definitions.Def_L22EigEst_SECond
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.6** (p.14), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "If S satisfies event E1, then we have that for all i ∈ [n], where the spectrum of
SA′_H S⊺ is padded with n − s zeros and sorted, |λi(SA′_H S⊺) − λi(A′_H)| ≤ 160L."

**Formalization Note.** `A′ = zeroed A ε`, `L = ε‖A‖_F/200`, `A′_H = highPart A′ L` (Definition 2.3 with
`λ = L`, p.13). Event E1 is `SECond A′ S L`. Deterministic in `S`, stated for every real diagonal
`S = diag(d)` (every sampling matrix in the `n × n` view is one); in that view `SA′_H S⊺` is
`n × n`, so its sorted spectrum is already padded with zeros. Stated for every `ε > 0`. -/
theorem lemma_4_6 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (ε : ℝ)
    (hε : 0 < ε) (d : Fin n → ℝ)
    (hE1 : SECond (zeroed A ε) (Matrix.diagonal d) (ε * frob A / 200)) :
    ∀ i, |gamma (Matrix.diagonal d *
              highPart (zeroed A ε) (zeroed_isHermitian hA ε) (ε * frob A / 200) *
              Matrix.diagonal d)
            (isHermitian_diag_conj d (highPart_isHermitian (zeroed_isHermitian hA ε) _)) i -
          gamma (highPart (zeroed A ε) (zeroed_isHermitian hA ε) (ε * frob A / 200))
            (highPart_isHermitian (zeroed_isHermitian hA ε) _) i| ≤
        160 * (ε * frob A / 200) := by sorry

end L22EigEst
