-- Prove2me | Theorems.Thm_GlobalSinkhorn_initial_potential
-- name    : GlobalSinkhorn.initial_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:01.69773+00:00
-- url     : https://prove2.me/theorems/1ecd0a5c-3c73-4b5f-9351-a2183bb93d8a
-- title:
--   Eq. (35) — the initial potential satisfies $\Phi(w_0)\le T^4-1$
-- statement:
--   Let $n\ge2$, let $x,y\in\mathbb R^n_{>0}$ and $T\in\mathbb R$ satisfy $T^{-1}\le x_iy_j\le T$ for all $i,j$, and put $w_0=Y^{-1}\mathbf 1$, i.e. $w_{0,j}=1/y_j$. Then
--   1. $w_{0,j}/w_{0,k}\le T^2$ for all $j,k$, so $\max_jw_{0,j}/\min_jw_{0,j}\le T^2$ (Eq. (35));
--   2. $\Phi(w_0)\le T^4-1$.
--
--   This bounds the starting potential of the Sinkhorn–Knopp dynamics by the product bound $T$ of the scaling.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - generalization: x, y the diagonal factors of a doubly stochastic scaling S = XAY with T ≥ 1 (context of Theorem 3.1) → any positive x, y and real T with T⁻¹ ≤ x_i y_j ≤ T for all i, j; no matrix and no T ≥ 1 hypothesis; reason: the page's argument uses only the product bounds; the hypotheses force T ≥ 1, and the context of Theorem 3.1 is a special case
--   - encoding: max_j w0,j / min_j w0,j ≤ T² → ∀ j k, (y j)⁻¹ / (y k)⁻¹ ≤ T ^ 2; reason: a bound on the largest ratio is a bound on every ratio
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Theorem 3.1, Eq. (35), pp.19–20

import Mathlib
import Definitions.Def_GlobalSinkhorn_potential

open Matrix

namespace GlobalSinkhorn

/-- Eq. (35) and the bound on the initial potential: for `w₀ = Y⁻¹1`, every ratio
`w₀,ⱼ / w₀,ₖ` is at most `T²`, and `Φ(w₀) ≤ T⁴ − 1`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Theorem 3.1, Eq. (35), pp.19–20.

**Formalization Note.** "`max w₀ / min w₀ ≤ T²`" is stated as a bound on every ratio. -/
theorem initial_potential {n : ℕ} (hn : 2 ≤ n) (x y : Fin n → ℝ) (T : ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hprod : ∀ i j, T⁻¹ ≤ x i * y j ∧ x i * y j ≤ T) :
    (∀ j k, (y j)⁻¹ / (y k)⁻¹ ≤ T ^ 2) ∧
      potential (fun j => (y j)⁻¹) ≤ T ^ 4 - 1 := by sorry

end GlobalSinkhorn
