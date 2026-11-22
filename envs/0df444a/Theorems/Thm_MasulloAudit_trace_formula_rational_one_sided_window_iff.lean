-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_one_sided_window_iff
-- name    : MasulloAudit.trace_formula_rational_one_sided_window_iff
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:56:00.011025+00:00
-- url     : https://prove2.me/theorems/92029645-ff06-4d45-9970-699cd8f7886e
-- title:
--   One-sided tests suffice: Masullo's Theorem 12.5.1.1 at window $\alpha$ for tests supported in $(1,\infty)$ holds iff all zeros satisfy $|\operatorname{Re}\rho-\tfrac12|<\alpha$
-- statement:
--   Fix $\alpha>0$. Restrict the window identity of Masullo's Theorem 12.5.1.1 in the $\zeta$ case (`MasulloRH.trace_formula_rational` at window $\alpha$, with its integrability and summability statements) to **one-sided** admissible tests, those supported in $(1,\infty)$. The restricted identity holds for all such tests **if and only if** every nontrivial zero $\rho$ of $\zeta$ satisfies $|\operatorname{Re}\rho-\tfrac12|<\alpha$.
--
--   So one-sided tests already detect every zero outside the window: restricting to $\operatorname{supp}\varphi\subset(1,\infty)$, the support condition of Thm 11.3.2.1, does not weaken the statement. This sharpens `MasulloAudit.trace_formula_rational_fixed_window_iff`. It also shows that one-sided trace obligations of this form, such as `MasulloRH.regular_width_one_sided_trace`, are exactly zero-free-strip statements.
--
--   **Formalization Note.** Same definitions and index types as `MasulloRH.trace_formula_rational`, with the extra hypothesis `tsupport φ ⊆ Ioi 1` on the tests.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520), Theorem 11.3.2.1 (p. 495).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- One-sided fixed-window form of Masullo, Theorem 12.5.1.1 (ζ case). For a fixed real
`α > 0`, the window identity of `MasulloRH.trace_formula_rational` at that `α` (with all its
convergence conjuncts) holds for every admissible test supported in `(1, ∞)` if and only if
every nontrivial zero `ρ` of the full critical strip satisfies `|Re ρ - 1/2| < α`. -/
theorem trace_formula_rational_one_sided_window_iff (α : ℝ) (hα : 0 < α) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ → tsupport φ ⊆ Ioi 1 →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) ↔
    ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < α := by sorry

end MasulloAudit
