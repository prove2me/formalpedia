-- Prove2me | Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
-- name    : MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T17:47:56.495855+00:00
-- url     : https://prove2.me/theorems/34a3ec4b-db41-4343-ad95-b9478883ac29
-- title:
--   Vanishing of the boundary-free upper-right omitted sum for nonnegative tests
-- statement:
--   Let $0<\alpha<1/2$, and suppose that the vertical line with real part $1/2+\alpha$ contains no zero of the Riemann zeta function with positive imaginary part. Let $\psi$ be a nonnegative smooth real-valued test function with compact support in $(0,\infty)$, such that $\psi(1)=0$ and $\psi(t^{-1})=\psi(t)$ for $t>0$. Write $\mathcal M\psi$ for its Mellin transform and $m(\rho)$ for the multiplicity of a zero. Show that
--   $$
--   \sum_{\substack{\zeta(\rho)=0,\ \Im\rho>0\\
--   1/2+\alpha\leq\Re\rho<1}}
--   m(\rho)\,\Re\bigl(\mathcal M\psi(\rho-1/2)\bigr)=0.
--   $$
--   This restricts the boundary-free cancellation problem to the nonnegative cone of the same inversion-even test space.
-- source:
--   Nonnegative-test specialization of https://prove2.me/theorems/0ad16d32-1282-455a-9121-1ce9a2395fd8 in the setting of A. M. Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520.

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero_nonneg
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hNonneg : ∀ t : ℝ, 0 ≤ ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by sorry
