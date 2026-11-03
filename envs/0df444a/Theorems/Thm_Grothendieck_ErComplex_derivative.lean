-- Prove2me | Theorems.Thm_Grothendieck_ErComplex_derivative
-- name    : Grothendieck.ErComplex_derivative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-02T16:04:35.430185+00:00
-- url     : https://prove2.me/theorems/7fe07c37-9180-40bb-82c0-8287cf8a42c4
-- title:
--   $E_r$ is holomorphic on the unit disc, with the termwise-differentiated series as derivative
-- statement:
--   The paper's function is the series $E_r(z)=\sum_k a_kz^{2k+1}$ with $a_k=C_r\frac{(1/2)_k(1/2)_k}{(r/2+1)_k k!}$, extended to the unit disc by the same formula. This node records that the extension is holomorphic there, with derivative given by the termwise-differentiated series:
--
--   $$
--   E_r'(z)=\sum_{k\ge0}a_k\,(2k+1)\,z^{2k},\qquad |z|<1.
--   $$
--
--   The point is not the value of the derivative but its *availability*: the contour argument of §3 integrates $w\,E_r'(w)/(E_r(w)-z)$ around the unit circle, and the Cauchy machinery needs $E_r$ to be complex-differentiable on the disc. The coefficients' decay $a_k\le C_r/(k+1)^2$ (published as `ErCoeff_decay_and_summable`) gives absolute convergence of the differentiated series on every compact sub-disc, hence holomorphy by the Weierstrass theorem for series.
--
--   **Formalization Note** A supporting lemma, not a verbatim statement of the paper; it is the analytic hypothesis of Lemma 3.2.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — equation (3.2), p. 88, and the contour argument of Lemma 3.2, p. 88.

import Mathlib
import Definitions.Def_Grothendieck_Series

open scoped BigOperators Real

namespace Grothendieck

/-- **`E_r` is holomorphic on the unit disc**, with the termwise-differentiated series as its
derivative. -/
theorem ErComplex_derivative (r : ℕ) (hr : 2 ≤ r) :
    DifferentiableOn ℂ (ErComplex r) (Metric.ball (0 : ℂ) 1) ∧
      ∀ z : ℂ, ‖z‖ < 1 →
        HasDerivAt (ErComplex r)
          (∑' k : ℕ, (ErCoeff r k : ℂ) * (((2 * k + 1 : ℕ) : ℂ) * z ^ (2 * k))) z := by sorry

end Grothendieck
