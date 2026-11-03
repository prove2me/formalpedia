-- Prove2me | Theorems.Thm_Grothendieck_integral_one_add_sq_rpow_neg
-- name    : Grothendieck.integral_one_add_sq_rpow_neg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T04:35:58.143698+00:00
-- url     : https://prove2.me/theorems/95dd8c82-e02d-4663-816e-636d4754a626
-- title:
--   The standard $p$-integral $\int_0^\infty(1+t^2)^{-M}dt=\tfrac12\Gamma(\tfrac12)\Gamma(M-\tfrac12)/\Gamma(M)$
-- statement:
--   For a real exponent $M>\tfrac12$,
--
--   $$
--   \int_0^\infty\frac{dt}{(1+t^2)^M}=\frac12\,\frac{\Gamma\big(\tfrac12\big)\,\Gamma\big(M-\tfrac12\big)}{\Gamma(M)} .
--   $$
--
--   This is the standard integral to which the paper's Step 3 reduces: with $A=\lVert X\rVert^2$ and $B$ the corresponding coefficient, the substitution $p=\sqrt{A/B}\,t$ gives $\int_0^\infty(A+Bp^2)^{-M}dp=\sqrt{A/B}\,A^{-M}\int_0^\infty(1+t^2)^{-M}dt$ (proved as `Grothendieck.integral_add_mul_sq_rpow_neg_eq`), so everything rests on this node. At $M=(r+2)/2$ it produces exactly the Beta factor $\tfrac12 B(\tfrac12,\tfrac{r+1}{2})$ of the paper.
--
--   The value is $\tfrac12 B(\tfrac12, M-\tfrac12)$: the substitution $t^2=u/(1-u)$ maps $(0,\infty)$ onto $(0,1)$ and carries the integrand to $\tfrac12 u^{-1/2}(1-u)^{M-3/2}$, whose integral is the Beta integral. Equivalently, writing $(1+t^2)^{-M}$ as a Gamma integral in a second variable and integrating out $t$ against the Gaussian $\int_0^\infty e^{-vt^2}dt=\tfrac12\sqrt{\pi/v}$ gives the same value, since $\Gamma(\tfrac12)=\sqrt\pi$.
--
--   **Formalization Note** A supporting lemma for Lemma 2.1, not a verbatim statement of the paper.
-- source:
--   Briët, de Oliveira Filho, Vallentin, *Grothendieck inequalities for semidefinite programs with rank constraint*, Theory of Computing 10(4), 2014, pp. 77-105 — Step 3 of the proof of Lemma 2.1, pp. 93-94.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The standard `p`-integral.** For `M > 1/2`,
`∫₀^∞ (1 + t²)^{-M} dt = ½ Γ(½) Γ(M - ½) / Γ(M)`. -/
theorem integral_one_add_sq_rpow_neg {M : ℝ} (hM : 1 / 2 < M) :
    (∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2) ^ (-M))
      = 1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (M - 1 / 2) / Real.Gamma M := by sorry

end Grothendieck
