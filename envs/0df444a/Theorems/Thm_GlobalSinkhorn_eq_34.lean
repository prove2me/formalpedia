-- Prove2me | Theorems.Thm_GlobalSinkhorn_eq_34
-- name    : GlobalSinkhorn.eq_34
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T04:23:33.843896+00:00
-- url     : https://prove2.me/theorems/a48910be-f38e-490f-bcf9-a7b63b745619
-- title:
--   Eq. (34) — $A^{(2t)}=M(w_t)$ with $w_0=Y^{-1}\mathbf 1$, $w_{t+1}=\mathcal F(w_t)$
-- statement:
--   Let $n\ge2$, let $A\in\mathbb R^{n\times n}_{\ge0}$ be row-stochastic, and suppose $S=XAY$ is doubly stochastic, where $X=\operatorname{diag}(x)$ and $Y=\operatorname{diag}(y)$ are positive diagonal matrices. Set
--   $$
--   w_0=Y^{-1}\mathbf 1,\qquad w_{t+1}=\mathcal F(w_t)\quad(t\ge0).
--   $$
--   Then for every $t\ge0$ the Sinkhorn–Knopp iterate after $t$ full column–row cycles is
--   $$
--   A^{(2t)}=M(w_t).
--   $$
--   This reduces the convergence of Sinkhorn–Knopp to the behaviour of the potential $\Phi(w_t)$.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - generalization: standing normalization min_i x_i = min_j y_j of the scaling factors (p.13) → not assumed: any positive x, y with S = XAY; reason: the normalized pair is a special case; for (cx, y/c) the start w₀ becomes c w₀, and F(cw) = cF(w), M(cw) = M(w), so the identity is the same
--   - encoding: A⁽⁰⁾ = A, then alternately normalize columns and rows; A⁽²ᵗ⁾ after t column–row cycles → skIter A (2 * t), with column step first and Lean's total division; reason: the denominators met are positive under the hypotheses (iterates are M(w_t), p.19), so total division never fires
--   - encoding: w_t defined recursively → (Fw S)^[t] (fun j => (y j)⁻¹); reason: the t-fold iterate of F applied to Y⁻¹1
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Theorem 3.1, Eq. (34), p.19

import Mathlib
import Definitions.Def_GlobalSinkhorn_IsPosDiagScaling
import Definitions.Def_GlobalSinkhorn_skIter
import Definitions.Def_GlobalSinkhorn_Mw
import Definitions.Def_GlobalSinkhorn_Fw

open Matrix

namespace GlobalSinkhorn

/-- Eq. (34): `A⁽²ᵗ⁾ = M(wₜ)`, where `w₀ = Y⁻¹1` and `wₜ₊₁ = F(wₜ)`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Theorem 3.1, Eq. (34), p.19. -/
theorem eq_34 {n : ℕ} (hn : 2 ≤ n) (A S : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ)
    (hA : A ∈ Matrix.rowStochastic ℝ (Fin n))
    (hS : S ∈ doublyStochastic ℝ (Fin n))
    (hxy : IsPosDiagScaling A S x y) (t : ℕ) :
    skIter A (2 * t) = Mw S ((Fw S)^[t] (fun j => (y j)⁻¹)) := by sorry

end GlobalSinkhorn
