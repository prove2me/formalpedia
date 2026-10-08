-- Prove2me | Theorems.Thm_Matrix_IsHermitian_sorted_eigenvalues_le_add_of_re_dotProduct_le
-- name    : Matrix.IsHermitian.sorted_eigenvalues_le_add_of_re_dotProduct_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T09:47:40.887603+00:00
-- url     : https://prove2.me/theorems/d9e36dac-f508-44a5-9a09-382d6d93d180
-- title:
--   Weyl's inequality: sorted eigenvalues of Hermitian matrices are monotone in the Loewner order
-- statement:
--   Let $A,B$ be Hermitian $n\times n$ matrices over $\mathbb{R}$ or $\mathbb{C}$ and $\varepsilon\in\mathbb{R}$ with
--   $$\operatorname{Re}\,x^*Ax\;\le\;\operatorname{Re}\,x^*Bx+\varepsilon\,|x|^2\qquad\text{for all }x,$$
--   i.e. $A\le B+\varepsilon I$. Then for the eigenvalues sorted in decreasing order (`eigenvalues₀`, which Mathlib proves antitone),
--   $$\lambda_j(A)\;\le\;\lambda_j(B)+\varepsilon\qquad\text{for every }j.$$
--   Proof idea (Courant–Fischer by a dimension count): if $\lambda_j(A)>\lambda_j(B)+\varepsilon$, the span $P$ of the first $j+1$ eigenvectors of $A$ (where $x^*Ax\ge\lambda_j(A)|x|^2$) and the span $R$ of the last $n-j$ eigenvectors of $B$ (where $x^*Bx\le\lambda_j(B)|x|^2$) meet only in $0$, but $\dim P+\dim R=n+1$.
-- source:
--   Weyl's monotonicity / perturbation inequality (H. Weyl, Math. Ann. 71 (1912)); see Horn–Johnson, Matrix Analysis, 2nd ed., Cor. 4.3.12. Mathlib (rev 0df444a) has sorted Hermitian eigenvalues but no min–max theorem.

import Mathlib.Analysis.Matrix.Spectrum

open Matrix

theorem Matrix.IsHermitian.sorted_eigenvalues_le_add_of_re_dotProduct_le {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) (ε : ℝ)
    (h : ∀ x : n → 𝕜, RCLike.re (star x ⬝ᵥ (A *ᵥ x)) ≤
      RCLike.re (star x ⬝ᵥ (B *ᵥ x)) + ε * RCLike.re (star x ⬝ᵥ x))
    (j : Fin (Fintype.card n)) : hA.eigenvalues₀ j ≤ hB.eigenvalues₀ j + ε := by sorry
