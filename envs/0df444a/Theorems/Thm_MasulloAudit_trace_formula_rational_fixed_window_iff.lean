-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_fixed_window_iff
-- name    : MasulloAudit.trace_formula_rational_fixed_window_iff
-- status  : Proved
-- author  : @lll
-- created : 2026-11-21T00:24:17.145609+00:00
-- url     : https://prove2.me/theorems/c7d3b4b4-1565-49fc-a645-3ee43eea9031
-- title:
--   Fixed window: Masullo's Theorem 12.5.1.1 at window $\alpha$ holds iff all zeros satisfy $|\operatorname{Re}\rho-\tfrac12|<\alpha$
-- statement:
--   Fix a real number $\alpha>0$. Consider the window identity of Masullo's Theorem 12.5.1.1 in the $\zeta$ case (formalized as `MasulloRH.trace_formula_rational`) for this single $\alpha$: for every admissible test $\varphi$ (smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$),
--
--   $$
--   \int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt+\sum_p\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr)=\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{|\operatorname{Re}\rho-\frac12|<\alpha}m_\rho\Phi(\rho-\tfrac12),
--   $$
--
--   together with its integrability and summability statements. This identity holds **if and only if every nontrivial zero $\rho$ of $\zeta$ satisfies $|\operatorname{Re}\rho-\tfrac12|<\alpha$.**
--
--   So for each fixed window the Main Theorem is exactly a zero-free-strip statement. This sharpens the all-$\alpha$ equivalence `MasulloRH.trace_formula_rational_iff_RH`. The companion result `MasulloAudit.trace_formula_rational_fixed_window_zero_free` records the consequence $\zeta(s)\neq0$ for $\tfrac12+\alpha\le\operatorname{Re}s<1$.
--
--   **Formalization Note.** Same definitions and index types as `MasulloRH.trace_formula_rational`. The right side quantifies over `ZetaZerosInTraceStrip (1/2)`, all zeros with $0<\operatorname{Re}\rho<1$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Fixed-window form of Masullo, Theorem 12.5.1.1 (ζ case). For a fixed real `α > 0`, the
window identity of `MasulloRH.trace_formula_rational` at that `α` (for every admissible test,
with all its convergence conjuncts) holds if and only if every nontrivial zero `ρ` of the full
critical strip satisfies `|Re ρ - 1/2| < α`. -/
theorem trace_formula_rational_fixed_window_iff (α : ℝ) (hα : 0 < α) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) ↔
    ∀ ρ : ZetaZerosInTraceStrip (1 / 2), |(ρ : ℂ).re - 1 / 2| < α := by sorry

end MasulloAudit
