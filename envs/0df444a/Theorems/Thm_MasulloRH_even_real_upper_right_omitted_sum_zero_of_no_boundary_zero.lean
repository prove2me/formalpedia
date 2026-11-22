-- Prove2me | Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero_of_no_boundary_zero
-- name    : MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T17:18:40.701467+00:00
-- url     : https://prove2.me/theorems/0ad16d32-1282-455a-9121-1ce9a2395fd8
-- title:
--   Vanishing of the upper-right omitted sum away from boundary zeros
-- statement:
--   Let $0<\alpha<1/2$. Assume that the vertical line with real part $1/2+\alpha$ contains no zero of the Riemann zeta function with positive imaginary part. Let $\psi$ be a smooth real-valued test function with compact support in $(0,\infty)$, with $\psi(1)=0$ and $\psi(t^{-1})=\psi(t)$ for $t>0$. Write $\mathcal M\psi$ for its Mellin transform and $m(\rho)$ for the multiplicity of a zeta zero. Show that
--   $$
--   \sum_{\substack{\zeta(\rho)=0,\ \Im\rho>0\\
--   1/2+\alpha\leq\Re\rho<1}}
--   m(\rho)\,\Re\bigl(\mathcal M\psi(\rho-1/2)\bigr)=0.
--   $$
--
--   This is the boundary-free cancellation problem in the Masullo trace-formula reduction. Cancellation at cutoffs with this boundary condition implies cancellation at every width by a limit from below.
-- source:
--   Boundary-free specialization of the Prove2Me reduction https://prove2.me/theorems/391d62e4-591a-4ffd-9e1a-27394b5e95ed, in the setting of Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520.

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.even_real_upper_right_omitted_sum_zero_of_no_boundary_zero
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by sorry
