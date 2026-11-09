-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_1
-- name    : L22EigEst.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:22:11.489205+00:00
-- url     : https://prove2.me/theorems/00863729-4f46-4dd9-9468-0972c9adeda1
-- title:
--   Lemma 4.1 — the zeroed matrix $A'$ moves every eigenvalue by at most $\varepsilon\|A\|_F$
-- statement:
--   Let $A\in\mathbb R^{n\times n}$ be symmetric and $\varepsilon\in(0,1)$, and let $A'$ be the matrix of equation (2), obtained from $A$ by zeroing the diagonal entries with $\|A_i\|_2^2\le\frac{\varepsilon^2}4\|A\|_F^2$ and the off-diagonal entries with $\|A_i\|_2^2\|A_j\|_2^2/\|A\|_F^2\le\frac{\varepsilon^2}{4}|A_{ij}|^2$. Then for every $i$,
--
--   $$|\lambda_i(A')-\lambda_i(A)|\le\varepsilon\|A\|_F ,$$
--
--   where eigenvalues are sorted non-increasingly.
--
--   The lemma is deterministic. It lets the analysis work with $A'$, whose entries are small relative to their row and column norms (Claim 4.17), at the cost of $\varepsilon\|A\|_F$, without the $\log n$ factor of earlier zeroing rules.
--
--   Differences from the source:
--   - encoding: λ_i, i ∈ [n], sorted non-increasingly → gamma _ _ i, i : Fin n (0-based); reason: Lean convention; same values
--   - encoding: off-diagonal test ‖A_i‖₂²‖A_j‖₂²/‖A‖_F² ≤ (ε²/4)|A_ij|² in (2) → ‖A_i‖₂²‖A_j‖₂² ≤ (ε²/4)|A_ij|²‖A‖_F² (zeroed); reason: multiplied out; equivalent for A ≠ 0, and at A = 0 every entry is 0 either way
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.1, p.13

import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_WainwrightHDS_EigPert_gamma

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.1** (Spectrum of A′, p.13), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "For any symmetric matrix A ∈ ℝ^{n×n} and ε ∈ (0, 1), the
symmetric matrix A′ ∈ ℝ^{n×n} formed according to (2) always satisfies the following property:
∀i : |λi(A′) − λi(A)| ≤ ε∥A∥F."

**Formalization Note.** `A′ = zeroed A ε`; eigenvalues are sorted (`gamma`, 0-based). -/
theorem lemma_4_1 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ i, |gamma (zeroed A ε) (zeroed_isHermitian hA ε) i - gamma A hA i| ≤ ε * frob A := by sorry

end L22EigEst
