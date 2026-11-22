-- Prove2me | Theorems.Thm_MasulloRH_even_real_upper_right_omitted_sum_zero
-- name    : MasulloRH.even_real_upper_right_omitted_sum_zero
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T13:36:23.697641+00:00
-- url     : https://prove2.me/theorems/391d62e4-591a-4ffd-9e1a-27394b5e95ed
-- title:
--   Vanishing of the upper-right omitted zero sum for real inversion-even trace tests
-- statement:
--   Let $0 < \alpha < \frac{1}{2}$ and let $\psi : \mathbb{R} \to \mathbb{R}$ be a real-valued inversion-even function ($\psi(t^{-1}) = \psi(t)$ for all $t > 0$) whose complex lift $\varphi(t) = \psi(t) \in \mathbb{C}$ satisfies `IsRationalTraceTest` $\varphi$. Writing $Q_\alpha^+ = \{\rho \in \mathbb{C} : \zeta(\rho) = 0,\; \tfrac{1}{2} + \alpha \le \operatorname{Re}(\rho) < 1,\; \operatorname{Im}(\rho) > 0\}$, the multiplicity-weighted real-part Mellin sum over $Q_\alpha^+$ vanishes:
--
--   $$
--   \sum_{\rho \in Q_\alpha^+} \mathrm{ord}_{\rho}(\zeta)\,\operatorname{Re}\!\left(\mathcal{M}\varphi\!\left(\rho - \tfrac{1}{2}\right)\right) = 0,
--   $$
--
--   where $\mathrm{ord}_\rho(\zeta) = \text{analyticOrderNatAt}\,\zeta\,\rho$ and $\mathcal{M}\varphi(s) = \int_0^\infty t^{s-1}\varphi(t)\,dt$.
--
--   **Formalization Note.** Combining this upper-right real-valued vanishing with four-fold symmetry (`MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right`), real–imaginary test decomposition, and the wide-window trace formula yields `MasulloRH.trace_formula_inversion_even`.
-- source:
--   Reduction child of MasulloRH.trace_formula_inversion_even (https://prove2.me/theorems/e0ea93eb-d7f1-427a-bb98-390ca375f326) via MasulloAudit.trace_formula_rational_of_half_le (https://prove2.me/theorems/aed6a888-6459-453b-a766-d090bf66aa44), MasulloAudit.trace_formula_window_with_remainder (https://prove2.me/theorems/44b878a5-cce3-4960-bb2f-a81125207f2c), and MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right (https://prove2.me/theorems/aa30ba75-33fb-4979-9c98-39ef864ee25e).

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.even_real_upper_right_omitted_sum_zero
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (ψ : ℝ → ℝ) (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    ∑' ρ : {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im},
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) *
        (mellin (fun t => (ψ t : ℂ)) ((ρ : ℂ) - 1 / 2)).re = 0 := by
  sorry
