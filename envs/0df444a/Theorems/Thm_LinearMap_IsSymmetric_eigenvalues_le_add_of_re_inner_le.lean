-- Prove2me | Theorems.Thm_LinearMap_IsSymmetric_eigenvalues_le_add_of_re_inner_le
-- name    : LinearMap.IsSymmetric.eigenvalues_le_add_of_re_inner_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-14T20:25:08.780975+00:00
-- url     : https://prove2.me/theorems/7757682a-d8a6-402e-aa6f-68242d743835
-- title:
--   Weyl's inequality: sorted eigenvalues of symmetric operators are monotone in the form order
-- statement:
--   Let $E$ be an inner product space over $\mathbb K\in\{\mathbb R,\mathbb C\}$ of finite dimension $m$, $\varepsilon\in\mathbb R$, and $T,S:E\to E$ symmetric linear maps with
--   $$\operatorname{Re}\langle Tx,x\rangle\le\operatorname{Re}\langle Sx,x\rangle+\varepsilon\|x\|^2\qquad(x\in E).$$
--   Then, with eigenvalues sorted in decreasing order, $\lambda_j(T)\le\lambda_j(S)+\varepsilon$ for every $j<m$.
--
--   This is the operator form of Weyl's monotonicity inequality; the matrix form for Hermitian matrices is published separately.
--
--   Formalization Note: `hT.eigenvalues hn : Fin m → ℝ` is Mathlib's `LinearMap.IsSymmetric.eigenvalues`, which is antitone (decreasing order).
-- source:
--   Weyl (1912); standard

import Mathlib

namespace LinearMap.IsSymmetric

open Module

/-- Let `T` and `S` be symmetric operators on an `m`-dimensional inner product space over `ℝ` or
`ℂ`, with `Re ⟪T x, x⟫ ≤ Re ⟪S x, x⟫ + ε ‖x‖²` for all `x`. Then for each `j`, the `j`-th
eigenvalue of `T` (eigenvalues in decreasing order) is at most the `j`-th eigenvalue of `S`
plus `ε`. -/
theorem eigenvalues_le_add_of_re_inner_le {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] {T S : E →ₗ[𝕜] E}
    {m : ℕ} (hT : T.IsSymmetric) (hS : S.IsSymmetric) (hn : finrank 𝕜 E = m) (ε : ℝ)
    (h : ∀ x : E, RCLike.re (inner 𝕜 (T x) x) ≤ RCLike.re (inner 𝕜 (S x) x) + ε * ‖x‖ ^ 2)
    (j : Fin m) :
    hT.eigenvalues hn j ≤ hS.eigenvalues hn j + ε := by
  sorry

end LinearMap.IsSymmetric
