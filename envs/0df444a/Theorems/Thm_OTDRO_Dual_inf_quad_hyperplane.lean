-- Prove2me | Theorems.Thm_OTDRO_Dual_inf_quad_hyperplane
-- name    : OTDRO.Dual.inf_quad_hyperplane
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T20:07:29.011247+00:00
-- url     : https://prove2.me/theorems/097ce444-d58a-4211-9ea5-10770f565086
-- title:
--   Proof of Theorem 1, p. 32 — quadratic minimum on a hyperplane
-- statement:
--   Let $Q$ be a positive definite $d\times d$ matrix, let $\beta\in\mathbb R^d$ be nonzero, and let $c\in\mathbb R$. The quadratic form has an attained minimum over the hyperplane $\beta^{\mathsf T}\Delta=c$:
--
--   $$\min_{\Delta:\,\beta^{\mathsf T}\Delta=c}\Delta^{\mathsf T}Q\Delta=\frac{c^2}{\beta^{\mathsf T}Q^{-1}\beta}.$$
--
--   This is the finite dimensional minimization used to reduce the pointwise transport envelope to one scalar variable in Theorem 1.
--
--   **Formalization Note** The result is stated as `IsLeast`, so it includes attainment. The nonzero condition makes the hyperplane nonempty and the denominator positive.
-- source:
--   arXiv:1810.02403v3, §5.1, proof of Theorem 1, p. 32, unnumbered quadratic-minimization display

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting

namespace OTDRO.Dual

open Matrix

/-- The quadratic minimization in the proof of Theorem 1, p. 32; the minimum is attained. -/
theorem inf_quad_hyperplane {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.PosDef)
    (β : EuclideanSpace ℝ (Fin d)) (hβ : β ≠ 0) (c : ℝ) :
    IsLeast
      {q : ℝ | ∃ Δ : EuclideanSpace ℝ (Fin d),
        inner ℝ β Δ = c ∧ q = dotProduct Δ.ofLp (Q *ᵥ Δ.ofLp)}
      (c ^ 2 / dotProduct β.ofLp (Q⁻¹ *ᵥ β.ofLp)) := by sorry

end OTDRO.Dual
