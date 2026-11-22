-- Prove2me | Theorems.Thm_MasulloAudit_window_remainder_ne_zero_of_omitted_zero
-- name    : MasulloAudit.window_remainder_ne_zero_of_omitted_zero
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:47:14.600958+00:00
-- url     : https://prove2.me/theorems/f1f37959-9158-488b-b151-c5663f9d85e7
-- title:
--   A zero outside the window forces a nonzero window remainder $R_\alpha$
-- statement:
--   Fix $\alpha>0$, and suppose some nontrivial zero $\rho_0$ of $\zeta$ lies outside the window, i.e. $|\operatorname{Re}\rho_0-\tfrac12|\ge\alpha$. Then there is an admissible test $\varphi$ (`MasulloRH.IsRationalTraceTest`) for which the window remainder
--
--   $$
--   R_\alpha(\varphi)=\sum_{|\operatorname{Re}\rho-\frac12|\ge\alpha}m_\rho\,\Phi(\rho-\tfrac12)
--   $$
--
--   is nonzero.
--
--   $R_\alpha$ is exactly the term separating Masullo's Theorem 12.5.1.1 (window $\alpha$) from the unconditional window explicit formula `MasulloAudit.trace_formula_window_with_remainder`. This theorem shows that $R_\alpha$ cannot be dropped as a formality. Unless every zero lies inside the window, any correct global-to-S-local passage (the missing §12.3, p. 514) must produce a nonzero remainder for some admissible test.
--
--   **Formalization Note.** Same definitions and index types as `MasulloRH.trace_formula_rational`. $R_\alpha$ is the sum over the subtype of `ZetaZerosInTraceStrip (1/2)` cut out by $\alpha\le|\operatorname{Re}\rho-\tfrac12|$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520), §12.3 (p. 514).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- The remainder `R_α(φ)` of the window explicit formula is not identically zero on admissible
tests whenever some nontrivial zero lies outside the open window, i.e. `α ≤ |Re ρ₀ - 1/2|`. -/
theorem window_remainder_ne_zero_of_omitted_zero (α : ℝ) (hα : 0 < α)
    (ρ₀ : ZetaZerosInTraceStrip (1 / 2)) (hρ₀ : α ≤ |(ρ₀ : ℂ).re - 1 / 2|) :
    ∃ φ : ℝ → ℂ, IsRationalTraceTest φ ∧
      (∑' ρ : {ρ : ZetaZerosInTraceStrip (1 / 2) | α ≤ |(ρ : ℂ).re - 1 / 2|},
        zetaTraceTerm φ (1 / 2) ρ) ≠ 0 := by sorry

end MasulloAudit
