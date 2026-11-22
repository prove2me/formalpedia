-- Prove2me | Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero_for_interval_positive_test
-- name    : MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T18:15:17.022396+00:00
-- url     : https://prove2.me/theorems/47cd30e2-8bf0-4ac1-bf95-b26314b5123e
-- title:
--   Omitted-sum cancellation for tests positive across one inversion-invariant interval
-- statement:
--   Let $0<\alpha<1/2$ and assume no zeta zero with positive imaginary part lies on the line $\Re s=1/2+\alpha$. Consider a smooth real nonnegative inversion-even test $\psi$ with compact support in $(0,\infty)$ and $\psi(1)=0$. Assume there is $0<r<1$ such that $\psi$ is positive exactly at the points $t\ne 1$ satisfying
--   $$
--   \frac{(t-1)^2}{1+t^2}<r.
--   $$
--   This is a single inversion-invariant interval with its midpoint in logarithmic coordinates removed. Show that the multiplicity-weighted sum of $\Re(\mathcal M\psi(\rho-1/2))$ over zeros with positive imaginary part and $1/2+\alpha\leq\Re\rho<1$ vanishes.
-- source:
--   Interval-positive test restriction of https://prove2.me/theorems/34a3ec4b-db41-4343-ad95-b9478883ac29, in the setting of A. M. Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520.

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_for_interval_positive_test
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (hStrict : ∀ t : ℝ, 0 < ψ t ↔ t ≠ 1 ∧ (t - 1) ^ 2 / (1 + t ^ 2) < r)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by sorry
