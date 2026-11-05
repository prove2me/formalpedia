-- Prove2me | Theorems.Thm_MultiParamQEC_eq_28_schur_matrix
-- name    : MultiParamQEC.eq_28_schur_matrix
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:02.216532+00:00
-- url     : https://prove2.me/theorems/10ee34f6-178c-4065-8872-258a390ff841
-- title:
--   Eq. (28), matrix form — $\begin{pmatrix}Y&K\\K&\mathbb 1\end{pmatrix}\ge0\iff Y\ge K^2$
-- statement:
--   For real $P\times P$ matrices $Y$ and $K$ with $K$ symmetric,
--   $$\begin{pmatrix}Y&K\\K&\mathbb 1_P\end{pmatrix}\ge0\iff Y\ge K^2 .$$
--   The printed (28), $\begin{pmatrix}w\mathbb 1_P&K\\K&\mathbb 1_P\end{pmatrix}\ge0\iff w\mathbb 1_P\ge K^2$, is the case $Y=w\mathbb 1_P$.
--
--   The matrix form is the one the corrected SDP (8) uses.
--
--   Differences from the source:
--   - generalization: the scalar block w 1_P, w ∈ ℝ → a real P × P matrix Y; reason: Y = w 1_P recovers the printed (28); the matrix form is what the corrected (8) needs
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.3, p.9, Eq. (28)

import Mathlib

open scoped Matrix

namespace MultiParamQEC

/-- **Second Schur-complement relation, matrix form** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Eq. (28), p.9: `[[w1_P, K], [K, 1_P]] ≥ 0 ⇔ w1_P ≥ K²`).

For real `P × P` matrices `Y` and `K` with `K` symmetric: `[[Y, K], [K, 1_P]]` is positive
semidefinite if and only if `Y − K²` is positive semidefinite. The printed (28) is the case
`Y = w 1_P`. -/
theorem eq_28_schur_matrix {P : ℕ} (Y K : Matrix (Fin P) (Fin P) ℝ) (hK : K.IsHermitian) :
    (Matrix.fromBlocks Y K K 1).PosSemidef ↔ (Y - K * K).PosSemidef := by sorry

end MultiParamQEC
