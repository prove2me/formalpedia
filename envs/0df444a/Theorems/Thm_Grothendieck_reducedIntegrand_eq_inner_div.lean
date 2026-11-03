-- Prove2me | Theorems.Thm_Grothendieck_reducedIntegrand_eq_inner_div
-- name    : Grothendieck.reducedIntegrand_eq_inner_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T22:21:25.803914+00:00
-- url     : https://prove2.me/theorems/ee369a1d-d26b-47d8-a42c-a1d8d40b8c21
-- title:
--   The rounding integrand is $\langle X,Y\rangle/(\lVert X\rVert\lVert Y\rVert)$
-- statement:
--   With $X=\sum_i W_{i0}e_i$ and $Y=\sum_i W_{i1}e_i$ the two columns of a random $r\times2$ matrix $W$, the integrand of the rank-three rounding step is the cosine of the angle between them, and this node records it in the form every integral computation uses:
--
--   $$
--   \mathrm{reducedIntegrand}_r(W)=\frac{\langle X,Y\rangle}{\lVert X\rVert\,\lVert Y\rVert}
--   =\langle X,Y\rangle\cdot(\lVert X\rVert\lVert Y\rVert)^{-1}.
--   $$
--
--   That is a rewriting of the definition — the integrand was defined as the inner product of the two *normalized* columns, $\langle X/\lVert X\rVert, Y/\lVert Y\rVert\rangle$ — together with the bilinearity of the inner product: pulling the two scalar factors $1/\lVert X\rVert$ and $1/\lVert Y\rVert$ out front multiplies them.
--
--   The point of stating it is that the denominator factor is exactly the singular factor that the Laplace step replaces by a smooth double integral (`Grothendieck.laplace_inv_sqrt_mul_inv_sqrt`). Splitting the integrand into a polynomial numerator and that denominator is what makes the Fubini step possible.
--
--   **Formalization Note** A supporting lemma, not a verbatim statement of the paper. `1/0 = 0` in Lean, so the identity also holds on the null set where a column vanishes.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Algorithm A, step 4 (p. 82) and Lemma 2.1 (p. 84).

import Mathlib
import Definitions.Def_Grothendieck_Reduced

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- The reduced integrand as a ratio: with `X`, `Y` the two columns of `W`,
`reducedIntegrand r W = ⟨X,Y⟩ · (‖X‖‖Y‖)⁻¹`. -/
theorem reducedIntegrand_eq_inner_div (r : ℕ) (W : Fin r → EuclideanSpace ℝ (Fin 2)) :
    reducedIntegrand r W
      = inner ℝ (colFun r 0 W) (colFun r 1 W)
        * (‖colFun r 0 W‖ * ‖colFun r 1 W‖)⁻¹ := by sorry

end Grothendieck
