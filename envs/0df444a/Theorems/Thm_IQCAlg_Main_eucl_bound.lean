-- Prove2me | Theorems.Thm_IQCAlg_Main_eucl_bound
-- name    : IQCAlg.Main.eucl_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T07:21:36.277692+00:00
-- url     : https://prove2.me/theorems/e815494d-16e9-46cd-8a7b-d20c86efcad3
-- title:
--   Proof of Theorem 4, p. 11 — from the P-weighted bound: ‖x_k − x⋆‖ ≤ √cond(P) ρᵏ ‖x_0 − x⋆‖
-- statement:
--   Let $P$ be a symmetric positive definite matrix, $\rho\ge 0$, and let $(x_k)$ be a sequence of vectors and $x_\star$ a vector such that
--
--   $$(x_k-x_\star)^\top P(x_k-x_\star)\le\rho^{2k}(x_0-x_\star)^\top P(x_0-x_\star)\qquad\text{for all }k.$$
--
--   Then, with $\|\cdot\|$ the Euclidean norm and $\operatorname{cond}(P)=\lambda_{\max}(P)/\lambda_{\min}(P)$,
--
--   $$\|x_k-x_\star\|\le\sqrt{\operatorname{cond}(P)}\,\rho^k\,\|x_0-x_\star\|\qquad\text{for all }k .$$
--
--   This converts decay in the $P$-weighted norm into decay in the Euclidean norm, at the price of the factor $\sqrt{\operatorname{cond}(P)}$ that appears in Theorem 4.
--
--   **Formalization Note.** The vectors are indexed by an arbitrary finite type. The norm is `norm2 v = √(v ⬝ᵥ v)`, not Mathlib's sup norm on functions.
-- source:
--   Lessard, Recht & Packard, Analysis and Design of Optimization Algorithms via Integral Quadratic Constraints, arXiv:1408.3595v7, p. 11, proof of Theorem 4, "and consequently ‖x_k − x⋆‖ ≤ √cond(P) ρ^k ‖x_0 − x⋆‖"

import Mathlib
import Definitions.Def_IQCAlg_Main_Setting

open Matrix

namespace IQCAlg.Main

/-- Proof of Theorem 4, the Euclidean bound, p. 11. If `P ≻ 0`, `ρ ≥ 0`, and a sequence `x`
satisfies `(x_k − x⋆)ᵀP(x_k − x⋆) ≤ ρ^{2k}(x₀ − x⋆)ᵀP(x₀ − x⋆)` for all `k`, then
`‖x_k − x⋆‖ ≤ √cond(P) ρ^k ‖x₀ − x⋆‖` for all `k` (2-norm). -/
theorem eucl_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Matrix ι ι ℝ) (hP : P.PosDef) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (x : ℕ → ι → ℝ) (xs : ι → ℝ)
    (hV : ∀ k : ℕ, qf P (x k - xs) ≤ ρ ^ (2 * k) * qf P (x 0 - xs)) :
    ∀ k : ℕ, norm2 (x k - xs) ≤ Real.sqrt (condNum P hP.isHermitian) * ρ ^ k * norm2 (x 0 - xs) := by sorry

end IQCAlg.Main
