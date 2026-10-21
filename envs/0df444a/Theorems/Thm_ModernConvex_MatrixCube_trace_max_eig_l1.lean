-- Prove2me | Theorems.Thm_ModernConvex_MatrixCube_trace_max_eig_l1
-- name    : ModernConvex.MatrixCube.trace_max_eig_l1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:47.150007+00:00
-- url     : https://prove2.me/theorems/7ef3dc01-e377-4237-8216-ec5b0b30b8af
-- title:
--   Lemma 4.4.3 — max Tr([U−V]A) over U,V ⪰ 0, U+V = W equals ‖λ(W^{1/2}AW^{1/2})‖₁
-- statement:
--   Let $W,A$ be symmetric $n\times n$ matrices with $W\succeq0$, and let $W^{1/2}$ be the positive semidefinite square root of $W$. Then
--   $$\max_{U,V\succeq0,\ U+V=W}\operatorname{Tr}([U-V]A)=\max_{X=X^T:\ \|\lambda(X)\|_\infty\le1}\operatorname{Tr}(XW^{1/2}AW^{1/2})=\|\lambda(W^{1/2}AW^{1/2})\|_1 ,$$
--   where $\lambda(\cdot)$ is the vector of eigenvalues of a symmetric matrix; in particular both maxima are attained.
--
--   This identity eliminates the variables $U^i,V^i$ from the dual of the problem behind $(S_\rho)$ in the proof of the Matrix Cube Theorem, and reappears in the reduction (4.4.49).
--
--   **Formalization Note** Each maximum is stated with `IsGreatest`: the value $\|\lambda(W^{1/2}AW^{1/2})\|_1$ belongs to the set of attainable traces and bounds it from above. $W^{1/2}$ is `CFC.sqrt W` under Mathlib's matrix order (`open scoped MatrixOrder`). $\|\lambda(X)\|_\infty\le1$ is written as $|\lambda_i(X)|\le1$ for every $i$.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 191, Lemma 4.4.3 (4.4.41)

import Mathlib
import Definitions.Def_ModernConvex_MatrixCube_MatrixCube

open Matrix
open scoped MatrixOrder

namespace ModernConvex.MatrixCube

/-- Ben-Tal–Nemirovski, Lemma 4.4.3, p. 191, (4.4.41): let `W, A ∈ Sⁿ` with `W ⪰ 0`, and let
`W^{1/2}` be the positive semidefinite square root of `W`. Then
`max_{U,V ⪰ 0, U+V=W} Tr([U − V]A) = max_{X=Xᵀ : ‖λ(X)‖_∞ ≤ 1} Tr(XW^{1/2}AW^{1/2})
  = ‖λ(W^{1/2}AW^{1/2})‖₁`.
Both maxima are stated as attained greatest values of the respective sets of traces. -/
theorem trace_max_eig_l1 {n : ℕ} (W A : Matrix (Fin n) (Fin n) ℝ) (hW : W.PosSemidef)
    (hA : A.IsHermitian) :
    IsGreatest {t : ℝ | ∃ U V : Matrix (Fin n) (Fin n) ℝ, U.PosSemidef ∧ V.PosSemidef ∧
        U + V = W ∧ t = ((U - V) * A).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) ∧
    IsGreatest {t : ℝ | ∃ X : Matrix (Fin n) (Fin n) ℝ, X.IsHermitian ∧
        (∀ i, |eigVec X i| ≤ 1) ∧ t = (X * (CFC.sqrt W * A * CFC.sqrt W)).trace}
      (eigL1 (CFC.sqrt W * A * CFC.sqrt W)) := by sorry

end ModernConvex.MatrixCube
