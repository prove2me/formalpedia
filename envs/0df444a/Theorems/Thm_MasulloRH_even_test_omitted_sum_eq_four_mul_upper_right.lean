-- Prove2me | Theorems.Thm_MasulloRH_even_test_omitted_sum_eq_four_mul_upper_right
-- name    : MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right
-- status  : Proved
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T13:34:53.778808+00:00
-- url     : https://prove2.me/theorems/aa30ba75-33fb-4979-9c98-39ef864ee25e
-- title:
--   Four-fold symmetry collapse of the omitted zero sum for real inversion-even trace tests
-- statement:
--   Let $\alpha > 0$, let $\psi : \mathbb{R} \to \mathbb{R}$ be a real-valued function satisfying $\psi(t^{-1}) = \psi(t)$ for all $t > 0$, and assume that its complex lift $\varphi(t) = \psi(t) \in \mathbb{C}$ is an admissible rational trace test function (`IsRationalTraceTest` $\varphi$: smooth, compactly supported in $(0, \infty)$, and vanishing at $1$). Define the omitted zero set in the critical strip and its upper-right quadrant restriction by
--
--   $$
--   R_\alpha = \left\{ \rho \in \mathbb{C} : \zeta(\rho) = 0,\; 0 < \operatorname{Re}(\rho) < 1,\; |\operatorname{Re}(\rho) - \tfrac{1}{2}| < \tfrac{1}{2},\; \alpha \le |\operatorname{Re}(\rho) - \tfrac{1}{2}| \right\},
--   $$
--   $$
--   Q_\alpha^+ = \left\{ \rho \in \mathbb{C} : \zeta(\rho) = 0,\; \tfrac{1}{2} + \alpha \le \operatorname{Re}(\rho) < 1,\; \operatorname{Im}(\rho) > 0 \right\}.
--   $$
--
--   Then the real-part zero sum over $Q_\alpha^+$ is unconditionally summable, and the full omitted spectral sum over $R_\alpha$ collapses to four times the real-part upper-right quadrant sum:
--
--   $$
--   \sum_{\rho \in R_\alpha} \mathrm{ord}_{\rho}(\zeta)\,\mathcal{M}\varphi\!\left(\rho - \tfrac{1}{2}\right)
--   = 4 \sum_{\rho \in Q_\alpha^+} \mathrm{ord}_{\rho}(\zeta)\,\operatorname{Re}\!\left(\mathcal{M}\varphi\!\left(\rho - \tfrac{1}{2}\right)\right),
--   $$
--
--   where $\mathrm{ord}_\rho(\zeta) = \text{analyticOrderNatAt}\,\zeta\,\rho$ is the multiplicity of $\rho$ and $\mathcal{M}\varphi(s) = \int_0^\infty t^{s-1}\varphi(t)\,dt$ is its Mellin transform.
--
--   **Formalization Note.** The equality holds in $\mathbb{C}$, with the upper-right sum expressed as a real `tsum` coerced into $\mathbb{C}$ and the remainder terms given by `zetaTraceTerm φ (1 / 2)`.
-- source:
--   Symmetry reduction of the omitted critical-strip zero remainder for MasulloRH.trace_formula_inversion_even (https://prove2.me/theorems/e0ea93eb-d7f1-427a-bb98-390ca375f326), proved via MasulloAudit.trace_formula_window_with_remainder (https://prove2.me/theorems/44b878a5-cce3-4960-bb2f-a81125207f2c), MasulloRH.riemannZeta_analyticOrderNatAt_one_sub (https://prove2.me/theorems/c6ad38df-324d-4b71-93b4-3bca44919e5c), and ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six (https://prove2.me/theorems/d1d6b916-b447-4dee-bd58-3bccf329d1d9).

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.even_test_omitted_sum_eq_four_mul_upper_right
    (α : ℝ) (hα : 0 < α) (ψ : ℝ → ℝ)
    (hψ : IsRationalTraceTest (fun t => (ψ t : ℂ)))
    (heven : ∀ t : ℝ, 0 < t → ψ t⁻¹ = ψ t) :
    let φ : ℝ → ℂ := fun t => (ψ t : ℂ)
    let remainder := {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|}
    let upperRight := {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 + α ≤ ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im}
    Summable (fun ρ : upperRight =>
      (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (mellin φ ((ρ : ℂ) - 1 / 2)).re) ∧
    ∑' ρ : remainder, zetaTraceTerm φ (1 / 2) ρ =
      4 * ((∑' ρ : upperRight,
        (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) * (mellin φ ((ρ : ℂ) - 1 / 2)).re : ℝ) : ℂ) := by
  sorry
