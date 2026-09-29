-- Prove2me | Theorems.Thm_LogRegretOCO_ONS_logdet_potential
-- name    : LogRegretOCO.ONS.logdet_potential
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T21:36:37.1864+00:00
-- url     : https://prove2.me/theorems/d0ed85cd-cac6-4c80-8659-1674d8d2967e
-- title:
--   Lemma 12 — A⁻¹ • (A − B) ≤ log(|A|/|B|) for A ⪰ B ≻ 0
-- statement:
--   For real $n\times n$ matrices $C,E$ write $C\bullet E=\sum_{i,j=1}^n C_{ij}E_{ij}$ for the entrywise (Frobenius) inner product and $|C|$ for the determinant. Let $A\succeq B\succ0$, i.e. $A-B$ is positive semidefinite and $B$ is positive definite (so $A$ is positive definite as well). Then
--   $$
--   A^{-1}\bullet(A-B)\ \le\ \log\frac{|A|}{|B|}.
--   $$
--
--   This is the matrix analogue of $\frac1a(a-b)\le\log\frac ab$ for $a>b>0$; summed over rounds it telescopes into a log-determinant and yields Lemma 11.
--
--   **Formalization Note** The product $\bullet$ is written out as the double sum $\sum_i\sum_j (A^{-1})_{ij}(A-B)_{ij}$, not Lean's scalar multiplication `•`. "$A\succeq B\succ0$" is encoded as `(A - B).PosSemidef ∧ B.PosDef`; the logarithm is the natural logarithm.
-- source:
--   Hazan, Agarwal, Kale, Logarithmic regret algorithms for online convex optimization, Mach Learn 69 (2007), p. 191, Lemma 12

import Mathlib

namespace LogRegretOCO.ONS

/-- Lemma 12 (Hazan–Agarwal–Kale 2007, p. 191). If `A ⪰ B ≻ 0` (i.e. `A − B` is positive
semidefinite and `B` is positive definite), then `A⁻¹ • (A − B) ≤ log(|A|/|B|)`, where
`C • E = Σ_{i,j} C_ij E_ij` is the entrywise (Frobenius) inner product and `|·|` the determinant. -/
theorem logdet_potential {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by sorry

end LogRegretOCO.ONS
