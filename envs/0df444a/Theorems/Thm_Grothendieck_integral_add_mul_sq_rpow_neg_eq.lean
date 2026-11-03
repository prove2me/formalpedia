-- Prove2me | Theorems.Thm_Grothendieck_integral_add_mul_sq_rpow_neg_eq
-- name    : Grothendieck.integral_add_mul_sq_rpow_neg_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T03:26:38.236262+00:00
-- url     : https://prove2.me/theorems/65bb2c91-f866-4d98-a416-aa87efc144c7
-- title:
--   Scaling step of the $p$-integral: $\int(A+Bp^2)^{-M}=\sqrt{A/B}\,A^{-M}\int(1+t^2)^{-M}$
-- statement:
--   For $A,B>0$ and a real exponent $M$,
--
--   $$
--   \int_0^\infty\frac{dp}{(A+Bp^2)^M}=\sqrt{\frac AB}\;A^{-M}\int_0^\infty\frac{dt}{(1+t^2)^M}.
--   $$
--
--   The substitution $p=\sqrt{A/B}\,t$ turns $A+Bp^2$ into $A(1+t^2)$ and $dp$ into $\sqrt{A/B}\,dt$, so the general `p`-integral of the paper's Step 3 reduces to the standard one $\int_0^\infty(1+t^2)^{-M}dt$. That standard integral is $\tfrac12\Gamma(\tfrac12)\Gamma(M-\tfrac12)/\Gamma(M)$, so the paper's formula $A^{1/2-M}B^{-1/2}\cdot\tfrac12 B(1/2,M-1/2)$ follows from this node and the evaluation of the standard case.
--
--   **Formalization Note** The substitution is the one-dimensional change of scale `integral_comp_mul_left_Ioi`; no convergence hypotheses are needed because the right-hand side is a real number identity (both sides are `0` by convention if the integrals diverge). Supporting lemma for Lemma 2.1.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Step 3 of the proof of Lemma 2.1, pp. 93-94.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Scaling step of the `p`-integral.** For `A, B > 0`,
`∫₀^∞ (A + B p²)^{-M} dp = √(A/B) A^{-M} ∫₀^∞ (1 + t²)^{-M} dt`. -/
theorem integral_add_mul_sq_rpow_neg_eq {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = Real.sqrt (A / B) * A ^ (-M) *
          ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M) := by sorry

end Grothendieck
