-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_1_8
-- name    : GlobalSinkhorn.Supplement.theorem_1_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:58:23.816254+00:00
-- url     : https://prove2.me/theorems/8793792a-0aff-4dfd-a2a8-c9a387ee0bce
-- title:
--   Theorem 1.8 — a $(1/2,1)$-dense family with $\sigma_n=1/2$ needing $\Omega(n^2)$ SK iterations
-- statement:
--   For every sufficiently large even integer $n$ there exists a $(1/2,1)$-dense matrix $D_n\in(0,1]^{n\times n}$ with the following properties.
--
--   1. Let $R_n=\operatorname{diag}(r_1(D_n),\dots,r_n(D_n))$ and $C_n=\operatorname{diag}(c_1(D_n),\dots,c_n(D_n))$ be the diagonal matrices of row and column sums and $E_n=R_n^{-1/2}D_nC_n^{-1/2}$. Then
--   $$\sigma_n=s_2(E_n)=\tfrac12.$$
--   2. Run Sinkhorn–Knopp from $A_n^{(0)}=R_n^{-1}D_n$, one normalization per iteration. If
--   $$
--   \sum_{i=1}^n\big|r_i(A_n^{(t)})-1\big|+\sum_{j=1}^n\big|c_j(A_n^{(t)})-1\big|\le\frac{1}{400n},
--   $$
--   then $t=\Omega(n^2)$.
--
--   At $\sigma=\gamma\rho=1/2$ the strict spectral condition of Theorem 1.7 cannot be relaxed to equality.
--
--   **Formalization Note** $\Omega(n^2)$ is one constant $c>0$ chosen, together with the threshold $N$, before $n$: for every even $n\ge N$ there is $D_n$ such that every iterate index $t$ with error at most $1/(400n)$ has $t\ge cn^2$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: for every sufficiently large even n there exists D_n …, t = Ω(n²) → ∃ c > 0, ∃ N, ∀ n ≥ N even, ∃ D_n, …, ∀ t, error ≤ 1/(400n) → c n² ≤ t; reason: the Ω-constant and the threshold are uniform in n, as the asymptotic statement requires
--   - encoding: E_n = R_n^{-1/2} D_n C_n^{-1/2} → normalizedMatrix D_n; reason: the matrix written out; entries are positive, so the sums are positive
--   - encoding: A_n^(0) = R_n⁻¹ D_n and the SK iterates A_n^(t), error Σ|r_i − 1| + Σ|c_j − 1| → marginalErr (skIter (rowNormalize D_n) t); reason: the published skIter (one normalization per index) and marginalErr; the row sums of D_n are positive
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 1.8, p.9

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_rowNormalize
import Definitions.Def_GlobalSinkhorn_skIter
import Definitions.Def_GlobalSinkhorn_marginalErr
import Definitions.Def_GlobalSinkhorn_Supplement_IsDense
import Definitions.Def_GlobalSinkhorn_Supplement_normalizedMatrix

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 1.8 (a critical dense family needing `Ω(n²)` iterations).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 1.8, p.9.

For every sufficiently large even `n` there is a `(1/2, 1)`-dense `Dₙ ∈ (0, 1]^{n×n}` with
(1) `σₙ = s₂(Rₙ^{-1/2} Dₙ Cₙ^{-1/2}) = 1/2` (`Rₙ`, `Cₙ` the diagonal matrices of row and column
sums), and (2) for the SK iterates from `Aₙ⁽⁰⁾ = Rₙ⁻¹ Dₙ`, whenever the total marginal `ℓ₁`
error of `Aₙ⁽ᵗ⁾` is at most `1/(400 n)`, `t = Ω(n²)`.

**Formalization Note.** `Ω(n²)` is one constant `c > 0`, chosen with the threshold `N` before
`n`: `∃ c > 0, ∃ N, ∀ even n ≥ N, ∃ Dₙ, … , ∀ t, err ≤ 1/(400n) → c n² ≤ t`. `t` counts single
normalizations (`skIter`, one normalization per iteration). `Rₙ⁻¹ Dₙ` is `rowNormalize Dₙ`
(positive row sums, so total division never fires). -/
theorem theorem_1_8 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n →
      ∃ D : Matrix (Fin n) (Fin n) ℝ,
        (∀ i j, 0 < D i j ∧ D i j ≤ 1) ∧ IsDense (1 / 2) 1 D ∧
        s2 (normalizedMatrix D) = 1 / 2 ∧
        ∀ t : ℕ, marginalErr (skIter (rowNormalize D) t) ≤ 1 / (400 * (n : ℝ)) →
          c * (n : ℝ) ^ 2 ≤ (t : ℝ) := by sorry

end GlobalSinkhorn.Supplement
