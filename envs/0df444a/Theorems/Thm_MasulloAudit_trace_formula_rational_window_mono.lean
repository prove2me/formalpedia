-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_window_mono
-- name    : MasulloAudit.trace_formula_rational_window_mono
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:51:13.860289+00:00
-- url     : https://prove2.me/theorems/796a89ec-4977-4ecd-8e39-bf26896c43c6
-- title:
--   Window monotonicity: Masullo's Theorem 12.5.1.1 at $\alpha$ implies it at every $\alpha'\ge\alpha$
-- statement:
--   Let $0<\alpha\le\alpha'$. If the window identity of Masullo's Theorem 12.5.1.1 in the $\zeta$ case (`MasulloRH.trace_formula_rational` for the single window $\alpha$, with its integrability and summability statements) holds for every admissible test $\varphi$, then it holds for the window $\alpha'$ as well.
--
--   By `MasulloAudit.trace_formula_rational_fixed_window_iff`, the window identity at $\alpha$ is equivalent to all nontrivial zeros satisfying $|\operatorname{Re}\rho-\tfrac12|<\alpha$. This condition is monotone in $\alpha$, so the instances of the Main Theorem become weaker as the window widens, and the strongest instances are the narrowest windows.
--
--   **Formalization Note.** Same definitions and index types as `MasulloRH.trace_formula_rational`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Window monotonicity for Masullo, Theorem 12.5.1.1 (ζ case). If the window identity of
`MasulloRH.trace_formula_rational` holds at some `α > 0` (for every admissible test, with all
its convergence conjuncts), then it also holds at every larger window `α' ≥ α`. -/
theorem trace_formula_rational_window_mono (α α' : ℝ) (hα : 0 < α) (hαα' : α ≤ α')
    (h : ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) :
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α') ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α', zetaTraceTerm φ α' ρ := by sorry

end MasulloAudit
