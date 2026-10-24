-- Prove2me | Theorems.Thm_OAI_SharpLiebThirring_MatrixProof_hilbertSchmidt_cfc_sub_le
-- name    : OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T13:57:21.575102+00:00
-- url     : https://prove2.me/theorems/71221339-91e1-4668-8e6d-c876ccce4c52
-- title:
--   Hilbert–Schmidt Lipschitz bound for the functional calculus of Hermitian matrices
-- statement:
--   **Setting.** $A$ and $B$ are Hermitian $n \times n$ complex matrices, indexed by a finite type, with eigenvalues $\lambda_i$ and $\nu_j$ (`Matrix.IsHermitian.eigenvalues`). For $f : \mathbb R \to \mathbb R$, $f(A)$ is the functional calculus `hA.cfc f`. The squared Hilbert–Schmidt (Frobenius) norm of a matrix $M$ is $\|M\|_{HS}^2 = \sum_{i,j} |M_{ij}|^2$.
--
--   **Statement.** Let $L \ge 0$, and suppose $f$ is $L$-Lipschitz between the two spectra: $|f(\lambda_i) - f(\nu_j)| \le L\,|\lambda_i - \nu_j|$ for all $i, j$. Then
--   $$\sum_{i,j} \bigl|(f(A) - f(B))_{ij}\bigr|^2 \;\le\; L^2 \sum_{i,j} \bigl|(A - B)_{ij}\bigr|^2,$$
--   that is, $\|f(A) - f(B)\|_{HS} \le L\,\|A - B\|_{HS}$.
--
--   This is the standard Hilbert–Schmidt estimate for the functional calculus that OpenAI's paper states as its Lemma 3.1 (Section 3.1). In eigenbases $(e_i)$ of $A$ and $(v_j)$ of $B$, the entries of the two differences are $(f(\lambda_i) - f(\nu_j))\langle e_i, v_j\rangle$ and $(\lambda_i - \nu_j)\langle e_i, v_j\rangle$. The hypothesis is needed only on pairs of eigenvalues, so the statement applies in particular to every $L$-Lipschitz $f$. The statement uses only Mathlib. Lean: `OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le`. It is OpenAI's lemma `hsSquared_cfc_sub` (in `lean/OAI/Analysis/LiebThirring/MatrixOrder.lean`), with OpenAI's `hsSquared` written out as the double sum of squared moduli of the entries.
-- source:
--   OpenAI, Sharp one-dimensional Lieb–Thirring constants, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 262; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Dimensional-Lieb-Thirring-Constants-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/LiebThirring/MatrixOrder.lean (declaration OAI.SharpLiebThirring.MatrixProof.hsSquared_cfc_sub)

import Mathlib

theorem OAI.SharpLiebThirring.MatrixProof.hilbertSchmidt_cfc_sub_le
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i j, |f (hA.eigenvalues i) - f (hB.eigenvalues j)| ≤
      L * |hA.eigenvalues i - hB.eigenvalues j|) :
    ∑ i, ∑ j, Complex.normSq ((hA.cfc f - hB.cfc f) i j) ≤
      L ^ 2 * ∑ i, ∑ j, Complex.normSq ((A - B) i j) := by
  sorry
