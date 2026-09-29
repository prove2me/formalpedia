-- Prove2me | Theorems.Thm_LogRegretOCO_FTAL_logdet_potential
-- name    : LogRegretOCO.FTAL.logdet_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:40:15.885178+00:00
-- url     : https://prove2.me/theorems/9de0829d-ba05-4873-9f78-549377a91ad6
-- title:
--   Lemma 12 — $A^{-1} \bullet (A - B) \le \log(|A|/|B|)$ for $A \succeq B \succ 0$
-- statement:
--   For $n \times n$ real matrices write $A \bullet B = \sum_{i,j=1}^n A_{ij} B_{ij}$ for the entrywise (Frobenius) inner product and $|A|$ for the determinant. Let $A, B$ be real symmetric matrices with $B$ positive definite and $A - B$ positive semidefinite (so $A \succeq B \succ 0$ and $A$ is positive definite as well). Then
--
--   $$
--   A^{-1} \bullet (A - B) \le \log \frac{|A|}{|B|}.
--   $$
--
--   This is the matrix analogue of $\frac1a (a - b) \le \log \frac ab$ for $a \ge b > 0$. It turns each term of the potential sum in Lemma 11 into a telescoping log-determinant ratio.
--
--   **Formalization Note** "$A \succeq B \succ 0$" is encoded as `(A - B).PosSemidef ∧ B.PosDef` (Mathlib's `PosSemidef`/`PosDef` include symmetry), and $\bullet$ is written as the literal double sum $\sum_{i}\sum_j (A^{-1})_{ij}(A-B)_{ij}$.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 191, Lemma 12 (Appendix 2); the product • is defined on p. 190

import Mathlib

namespace LogRegretOCO.FTAL
theorem logdet_potential {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by sorry
end LogRegretOCO.FTAL
