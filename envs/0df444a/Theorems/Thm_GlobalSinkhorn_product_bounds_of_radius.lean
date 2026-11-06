-- Prove2me | Theorems.Thm_GlobalSinkhorn_product_bounds_of_radius
-- name    : GlobalSinkhorn.product_bounds_of_radius
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:09.406845+00:00
-- url     : https://prove2.me/theorems/58a52d37-e822-4e62-866f-8c2a2d5ec50e
-- title:
--   Proof of Theorem 1.1 — product bounds $e^{-2D}\le x_iy_j\le e^{2D}$ from a minimizing pair
-- statement:
--   Let $n\ge2$, let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic, and let $B$ be a doubly stochastic positive diagonal scaling of $A$; write $D=D(A;B)$. Then there are positive vectors $x,y\in\mathbb R^n_{>0}$ such that
--   1. $B=XAY$ with $X=\operatorname{diag}(x)$, $Y=\operatorname{diag}(y)$;
--   2. $\min_ix_i=\min_jy_j$;
--   3. for every pair of indices $i,j$,
--   $$
--   e^{-2D}\le x_iy_j\le e^{2D}.
--   $$
--
--   The bounds hold for all index pairs, including those outside the support of $A$. This is the step that turns the scaling radius into the product bound $T=e^{2D}$ required by Theorem 3.1.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: the pair X = a·diag(e^u), Y = a⁻¹·diag(e^{−v}) built from a minimizing pair (u, v) → ∃ x y with the three properties; reason: the minimizing pair is not unique, so the page's claim about the constructed pair is an existence statement; Theorem 3.1 consumes only existence
--   - encoding: min_i x_i, min_j y_j → ⨅ i, x i and ⨅ j, y j over the nonempty finite type Fin n; reason: on a nonempty finite index set the real infimum is the minimum
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Theorem 1.1, p.21

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_scalingRadius

open Matrix

namespace GlobalSinkhorn

/-- A minimizing pair of Definition 2.1, returned to the normalization `min x = min y`, gives
`e^{-2D} ≤ xᵢ yⱼ ≤ e^{2D}` for all index pairs. He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Theorem 1.1, p.21.

**Formalization Note.** On the nonempty finite type `Fin n` the real `⨅` is the minimum. -/
theorem product_bounds_of_radius {n : ℕ} (hn : 2 ≤ n) (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hB : B ∈ doublyStochastic ℝ (Fin n))
    (hAB : ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y) :
    ∃ x y : Fin n → ℝ, IsPosDiagScaling A B x y ∧ (⨅ i, x i) = (⨅ j, y j) ∧
      ∀ i j, Real.exp (-(2 * scalingRadius A B)) ≤ x i * y j ∧
        x i * y j ≤ Real.exp (2 * scalingRadius A B) := by sorry

end GlobalSinkhorn
