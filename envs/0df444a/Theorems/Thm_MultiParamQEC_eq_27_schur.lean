-- Prove2me | Theorems.Thm_MultiParamQEC_eq_27_schur
-- name    : MultiParamQEC.eq_27_schur
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:36:59.681654+00:00
-- url     : https://prove2.me/theorems/90aa6158-d23b-4756-acb4-63177e4149c3
-- title:
--   Eq. (27) — $\begin{pmatrix}K&\mathbb 1\\\mathbb 1&M\end{pmatrix}\ge0\iff M>0$ and $K\ge M^{-1}$
-- statement:
--   For real $P\times P$ matrices $K$ and $M$,
--   $$\begin{pmatrix}K&\mathbb 1_P\\\mathbb 1_P&M\end{pmatrix}\ge0\iff M>0\ \text{and}\ K\ge M^{-1}.$$
--   On the page $M=\Gamma\sqrt{W^{-1}}$.
--
--   Together with (28) it expresses the objective $\mathrm{Tr}(W(\Gamma^T\Gamma)^{-1})$ of (26) by linear matrix inequalities.
--
--   Differences from the source:
--   - generalization: M = Γ√(W⁻¹), positive semidefinite by Sec. 4.2.3, with (Γ√(W⁻¹))⁻¹ presupposed to exist; right side K ≥ (Γ√(W⁻¹))⁻¹ → any real P × P matrix M; right side M positive definite ∧ K − M⁻¹ positive semidefinite; reason: the left side forces M positive definite, so for the page's M ≥ 0 the clause M > 0 is the invertibility the page presupposes; the statement specializes to (27)
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.3, p.9, Eq. (27)

import Mathlib

open scoped Matrix

namespace MultiParamQEC

/-- **First Schur-complement relation** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Eq. (27), p.9: `[[K, 1_P], [1_P, Γ√(W⁻¹)]] ≥ 0 ⇔ K ≥ (Γ√(W⁻¹))⁻¹`).

For real `P × P` matrices `K` and `M`: `[[K, 1_P], [1_P, M]]` is positive semidefinite if and only
if `M` is positive definite and `K − M⁻¹` is positive semidefinite.

**Formalization Note.** On the page `M = Γ√(W⁻¹)` is positive semidefinite (Sec. 4.2.3) and
`(Γ√(W⁻¹))⁻¹` presupposes it invertible; the statement holds for every real `M` and says that the
left side forces `M` positive definite, so Mathlib's junk inverse `0` of a singular `M` never
enters. Positive (semi)definiteness over `ℝ` includes symmetry. -/
theorem eq_27_schur {P : ℕ} (K M : Matrix (Fin P) (Fin P) ℝ) :
    (Matrix.fromBlocks K 1 1 M).PosSemidef ↔ M.PosDef ∧ (K - M⁻¹).PosSemidef := by sorry

end MultiParamQEC
