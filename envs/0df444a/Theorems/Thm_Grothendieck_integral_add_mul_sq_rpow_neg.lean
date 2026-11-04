-- Prove2me | Theorems.Thm_Grothendieck_integral_add_mul_sq_rpow_neg
-- name    : Grothendieck.integral_add_mul_sq_rpow_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T07:09:37.39127+00:00
-- url     : https://prove2.me/theorems/677aedfe-1389-4b99-9c2e-56483dd839ab
-- title:
--   The paper's $p$-integral: $\int(A+Bp^2)^{-M}=A^{\frac12-M}B^{-\frac12}\,\frac12\Gamma(\tfrac12)\Gamma(M-\tfrac12)/\Gamma(M)$
-- statement:
--   For $A,B>0$ and $M>\tfrac12$,
--
--   $$
--   \int_0^\infty\frac{dp}{(A+Bp^2)^M}=A^{\frac12-M}B^{-\frac12}\cdot\frac12\,\frac{\Gamma(\tfrac12)\Gamma(M-\tfrac12)}{\Gamma(M)} .
--   $$
--
--   This is the paper's Step 3: the integral that the two Laplace parameters produce after the row-wise Gaussian integration. Two published nodes compose into it — the scaling $\int_0^\infty(A+Bp^2)^{-M}dp=\sqrt{A/B}\,A^{-M}\int_0^\infty(1+t^2)^{-M}dt$, and the standard value $\int_0^\infty(1+t^2)^{-M}dt=\tfrac12\Gamma(\tfrac12)\Gamma(M-\tfrac12)/\Gamma(M)$ — with $\sqrt{A/B}=\sqrt A/\sqrt B=A^{1/2}B^{-1/2}$ supplying the prefactor.
--
--   At $M=(r+2)/2$ this is exactly the factor $\tfrac12 B(\tfrac12,\tfrac{r+1}{2})$ times $A^{-(r+1)/2}B^{-1/2}$ that the paper's Lemma 2.1 displays, which is why it is the step that reduces the expectation to a Beta integral.
--
--   **Formalization Note** A supporting lemma for Lemma 2.1, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Step 3 of the proof of Lemma 2.1, pp. 93-94.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The paper's `p`-integral.** For `A, B > 0` and `M > 1/2`,
`∫₀^∞ (A + B p²)^{-M} dp = A^{1/2-M} B^{-1/2} ½ Γ(½) Γ(M-½)/Γ(M)`. -/
theorem integral_add_mul_sq_rpow_neg {A B M : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 1 / 2 < M) :
    (∫ p in Set.Ioi (0:ℝ), (A + B * p ^ 2) ^ (-M))
      = A ^ (1 / 2 - M) * B ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M) := by sorry

end Grothendieck
