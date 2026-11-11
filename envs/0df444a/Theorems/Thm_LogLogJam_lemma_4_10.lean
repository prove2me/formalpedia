-- Prove2me | Theorems.Thm_LogLogJam_lemma_4_10
-- name    : LogLogJam.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:23:33.097057+00:00
-- url     : https://prove2.me/theorems/7806a6a6-69ab-4060-8216-59cbfbadae4e
-- title:
--   Lemma 4.10 — $\det\frac{V_K+V_{K'}}2=\frac{|\det(I-K^\dagger K')|^2}{\det(I-KK^\dagger)\det(I-K'K'^\dagger)}$
-- statement:
--   For all $K,K'$ in the Siegel disk $\mathfrak D_k$,
--
--   $$
--   \det\Big(\frac{V_K+V_{K'}}2\Big)=\frac{|\det(I_k-K^\dagger K')|^2}{\det(I_k-KK^\dagger)\,\det(I_k-K'K'^\dagger)} .
--   $$
--
--   It expresses the overlap of two pure Gaussian states in Siegel coordinates and, in the proof of Lemma 6.1, makes $\int_0^\pi\log\det(V_\theta^{\oplus k}+W)\,d\theta$ computable.
--
--   Differences from the source:
--
--   - encoding: $\det(I_k-KK^\dagger)$ in the denominator → its real part; reason: the determinant of a positive definite Hermitian matrix is a positive real number
--   - encoding: $V_K$, the covariance of $|\psi_K\rangle$ → the formula of Lemma 4.6; reason: Lemma 4.6
-- source:
--   Chen, Gong, Ye, Zhang, The log log jam in Gaussian state tomography, arXiv:2607.12983 (version of November 3, 2026, sha256 97b751ca…), Lemma 4.10, p.21 (PDF p.24)

import Mathlib
import Definitions.Def_LogLogJam_VK

open Matrix

namespace LogLogJam

/-- **Lemma 4.10** (arXiv:2607.12983, version of November 3, 2026, sha256 97b751ca…, Lemma 4.10, p.21): "For all K, K' ∈ D_k,
det((V_K + V_{K'})/2) = |det(I_k − K†K')|² / (det(I_k − KK†) det(I_k − K'K'†))."

**Formalization Note** `det(I − KK†)` is the determinant of a positive definite Hermitian matrix,
a positive real number; its real part is taken. -/
theorem lemma_4_10 {k : ℕ} (K K' : Matrix (Fin k) (Fin k) ℂ) (hK : InSiegelDisk K)
    (hK' : InSiegelDisk K') :
    ((1 / 2 : ℝ) • (VK K + VK K')).det =
      Complex.normSq (1 - Kᴴ * K').det / ((1 - K * Kᴴ).det.re * (1 - K' * K'ᴴ).det.re) := by sorry

end LogLogJam
