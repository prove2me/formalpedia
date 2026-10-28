-- Prove2me | Theorems.Thm_Matrix_shermanMorrison_quadForm
-- name    : Matrix.shermanMorrison_quadForm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:38.03725+00:00
-- url     : https://prove2.me/theorems/1a366b9f-eb15-4c7e-bade-c748e334e525
-- title:
--   Rank-one update of a quadratic form (Sherman–Morrison)
-- statement:
--   Let $V$ be a positive definite real $d \times d$ matrix, let $x, S \in \mathbb{R}^d$ and
--   let $e \in \mathbb{R}$. Write $x x^{\mathsf T}$ for the rank-one matrix with entries $x_i x_j$.
--   Then the quadratic form of the inverse of the rank-one update $V + x x^{\mathsf T}$, evaluated at
--   the shifted vector $S + e x$, has the closed form
--
--   $$
--   (S + e x)^{\mathsf T} \bigl(V + x x^{\mathsf T}\bigr)^{-1} (S + e x)
--   \;=\; S^{\mathsf T} V^{-1} S \;+\;
--   \frac{2 e\, (x^{\mathsf T} V^{-1} S) \;+\; e^{2}\,(x^{\mathsf T} V^{-1} x) \;-\; (x^{\mathsf T} V^{-1} S)^{2}}
--        {1 \;+\; x^{\mathsf T} V^{-1} x}.
--   $$
--
--   Everything on the right is expressed through $V^{-1}$ alone, so a rank-one update of the matrix
--   costs no new inversion. This is the Sherman–Morrison identity in the form a recursive
--   algorithm needs: in recursive least squares, in Kalman filtering and in linear bandit methods a
--   single observation updates the design matrix by $x x^{\mathsf T}$ and shifts the response
--   accumulator by $e x$, and the quantity on the left is the next value of the self-normalized
--   statistic.
--
--   **Formalization Note** $x x^{\mathsf T}$ is `Matrix.vecMulVec x x`, the quadratic form is
--   written with `dotProduct` and `mulVec`, and positive definiteness of $V$ is `Matrix.PosDef`.
-- source:
--   J. Sherman and W. J. Morrison, Adjustment of an inverse matrix corresponding to a change in one element of a given matrix, Ann. Math. Statist. 21 (1950), 124–127; carved from the accepted proof of ImprovedLinBandits.OFUL.oful_regret_bound, https://prove2.me/submissions/028e111f-382d-40d0-8008-127228d5e6cf

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
open MeasureTheory ProbabilityTheory Matrix NNReal

theorem Matrix.shermanMorrison_quadForm {d : ℕ} {V : Matrix (Fin d) (Fin d) ℝ} (hV : V.PosDef) (x S : Fin d → ℝ)
    (e : ℝ) :
    (S + e • x) ⬝ᵥ (V + vecMulVec x x)⁻¹ *ᵥ (S + e • x) =
      S ⬝ᵥ V⁻¹ *ᵥ S + (2 * e * (x ⬝ᵥ V⁻¹ *ᵥ S) + e ^ 2 * (x ⬝ᵥ V⁻¹ *ᵥ x)
        - (x ⬝ᵥ V⁻¹ *ᵥ S) ^ 2) / (1 + x ⬝ᵥ V⁻¹ *ᵥ x) := by sorry
