-- Prove2me | Theorems.Thm_Grothendieck_integral_kernel_inner
-- name    : Grothendieck.integral_kernel_inner
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T20:42:16.22368+00:00
-- url     : https://prove2.me/theorems/cfd22b7f-2b8d-4331-b461-7a4b52d5c343
-- title:
--   Step 5 of Lemma 2.1: the inner v-integral in closed form
-- statement:
--   For r >= 2 and |tau| < 1, the integral over v>0 of ((1+u^2)(1+v^2) - tau^2 u^2 v^2)^{-(r+2)/2} equals A^{1/2-M} B^{-1/2} (1/2) Gamma(1/2) Gamma(M-1/2) / Gamma(M), where A = 1+u^2, B = 1+(1-tau^2)u^2 and M = (r+2)/2. The identity (1+u^2)(1+v^2) - tau^2u^2v^2 = A + B v^2 puts the integrand in the shape of the paper p-integral, whose value is the published formula. This is step 3 of Lemma 2.1 after the substitutions s=p^2/2, t=q^2/2.
-- source:
--   Briet, de Oliveira Filho, Vallentin, Theory of Computing 10(4), 2014, pp. 77-105 - step 3 of the proof of Lemma 2.1.

import Mathlib

open MeasureTheory
open scoped BigOperators Real

namespace Grothendieck

/-- **Step 5 of Lemma 2.1: the inner (`v`-)integral.** For `r ≥ 2`, `|τ| < 1` and any `u`,
`∫₀^∞ ((1+u²)(1+v²) - τ²u²v²)^{-(r+2)/2} dv = A^{1/2-M} B^{-1/2} ½Γ(½)Γ(M-½)/Γ(M)` with
`A = 1+u²`, `B = 1+(1-τ²)u²`, `M = (r+2)/2`. -/
theorem integral_kernel_inner (r : ℕ) (hr : 2 ≤ r) {τ : ℝ} (hτ : τ ^ 2 < 1) (u : ℝ) :
    (∫ v in Set.Ioi (0:ℝ),
        ((1 + u ^ 2) * (1 + v ^ 2) - τ ^ 2 * u ^ 2 * v ^ 2) ^ (-(((r : ℝ) + 2) / 2) : ℝ))
      = (1 + u ^ 2) ^ (1 / 2 - ((r : ℝ) + 2) / 2) *
          (1 + (1 - τ ^ 2) * u ^ 2) ^ (-(1 / 2) : ℝ) *
          (1 / 2 * Real.Gamma (1 / 2) * Real.Gamma (((r : ℝ) + 2) / 2 - 1 / 2) /
            Real.Gamma (((r : ℝ) + 2) / 2)) := by sorry

end Grothendieck
