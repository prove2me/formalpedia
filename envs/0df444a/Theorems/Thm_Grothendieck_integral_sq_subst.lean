-- Prove2me | Theorems.Thm_Grothendieck_integral_sq_subst
-- name    : Grothendieck.integral_sq_subst
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T14:54:18.39608+00:00
-- url     : https://prove2.me/theorems/6e91c90d-ba7d-4f93-8bdc-81d34da4d7c3
-- title:
--   The $q^2=x/(1-x)$ substitution of Lemma 2.1
-- statement:
--   For $|\tau|<1$, the integral identity recorded here is the last change of variables of Lemma 2.1: the surviving $q$-integrand $(1+q^2)^{1/2-M}(1+(1-\tau^2)q^2)^{-1/2}$ becomes a Beta-type integral over $(0,1)$ under $x=q^2/(1+q^2)$, with $1+q^2=1/(1-x)$, $1+(1-\tau^2)q^2=(1-\tau^2x)/(1-x)$ and $dq=\tfrac12x^{-1/2}(1-x)^{-3/2}dx$; the powers of $(1-x)$ combine to $M-\tfrac32$.
--
--   **Formalization Note** Supporting lemma for Lemma 2.1.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - final substitution in the proof of Lemma 2.1.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **The `q² = x/(1-x)` substitution.** For `|τ| < 1`,
`∫₀^∞ (1+q²)^{1/2-M}(1+(1-τ²)q²)^{-1/2} dq = ½∫₀^1 x^{-1/2}(1-x)^{M-3/2}(1-τ²x)^{-1/2} dx`. -/
theorem integral_sq_subst {M τ : ℝ} (hM : 1 / 2 < M) (hτ : |τ| < 1) :
    (∫ q in Set.Ioi (0:ℝ), (1 + q ^ 2) ^ (1 / 2 - M) *
        (1 + (1 - τ ^ 2) * q ^ 2) ^ (-(1 / 2) : ℝ))
      = 1 / 2 * ∫ x in Set.Ioo (0:ℝ) 1,
          x ^ (-(1 / 2) : ℝ) * (1 - x) ^ (M - 3 / 2) * (1 - τ ^ 2 * x) ^ (-(1 / 2) : ℝ) := by sorry

end Grothendieck
