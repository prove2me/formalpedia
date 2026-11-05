-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_primal_separation
-- name    : ModernConvex.Relaxations.primal_separation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:34:37.876963+00:00
-- url     : https://prove2.me/theorems/e1663e3e-7f46-4bd8-8563-f2cce925ba71
-- title:
--   A negative direction separates a symmetric matrix from the PSD cone
-- statement:
--   **A negative direction separates a matrix from the positive semidefinite cone.**
--
--   Let $X$ be real symmetric and suppose $v^{\mathsf T}Xv<0$. Then $W=-vv^{\mathsf T}\neq0$, and for every $Y\succeq0$,
--   $$\langle Y-X,W\rangle=\sum_{i,j}(Y_{ij}-X_{ij})\left(-v_iv_j\right)=v^{\mathsf T}Xv-v^{\mathsf T}Yv\le v^{\mathsf T}Xv<0,$$
--   using $v^{\mathsf T}Zv=\sum_{i,j}Z_{ij}v_iv_j$ and $v^{\mathsf T}Yv\ge0$. So the half-space through $X$ with normal $W$ contains the whole semidefinite cone, which is the cut the ellipsoid method needs.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, (4.3.15), p. 170; the cut used by the ellipsoid method on the primal body.

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix
open scoped BigOperators

namespace ModernConvex.Relaxations

/-- **The separation step for the semidefinite constraint.** If `X` is symmetric and not positive
semidefinite, then `W := −v vᵀ` is a nonzero matrix whose Frobenius pairing with `Y − X` is
nonpositive for every positive semidefinite `Y`. -/
theorem primal_separation {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian)
    (h : ¬ X.PosSemidef) :
    ∃ W : Matrix (Fin n) (Fin n) ℝ, W ≠ 0 ∧
      ∀ Y : Matrix (Fin n) (Fin n) ℝ, Y.PosSemidef →
        (∑ i, ∑ j, (Y - X) i j * W i j) ≤ 0 := by sorry

end ModernConvex.Relaxations
