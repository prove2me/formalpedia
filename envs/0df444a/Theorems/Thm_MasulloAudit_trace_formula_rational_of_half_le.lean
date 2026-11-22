-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_of_half_le
-- name    : MasulloAudit.trace_formula_rational_of_half_le
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:25:47.106452+00:00
-- url     : https://prove2.me/theorems/aed6a888-6459-453b-a766-d090bf66aa44
-- title:
--   Masullo's Theorem 12.5.1.1 holds unconditionally for every window $\alpha\ge\tfrac12$
-- statement:
--   For every $\alpha\ge\tfrac12$, the window identity of Masullo's Theorem 12.5.1.1 in the $\zeta$ case (`MasulloRH.trace_formula_rational`) holds unconditionally. For every admissible test $\varphi$ (smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$), the real-place integrand is integrable, the prime-power and zero families are summable, and
--
--   $$
--   \int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt+\sum_p\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr)=\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{|\operatorname{Re}\rho-\frac12|<\alpha}m_\rho\Phi(\rho-\tfrac12).
--   $$
--
--   All nontrivial zeros satisfy $0<\operatorname{Re}\rho<1$, so a window of half-width $\alpha\ge\tfrac12$ contains all of them, and the identity is Weil's explicit formula. Together with `MasulloAudit.trace_formula_rational_fixed_window_iff`, this shows the Main Theorem's content is concentrated in windows $\alpha<\tfrac12$. Each such window is equivalent to a zero-free strip, and the conjunction over all $\alpha>0$ is equivalent to RH.
--
--   **Formalization Note.** Same definitions and index types as `MasulloRH.trace_formula_rational`, whose own statement requires only $\alpha>0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1 (pp. 519-520).

import Definitions.Def_MasulloRH_RationalTrace

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Masullo, Theorem 12.5.1.1 (ζ case) holds unconditionally for every window α ≥ 1/2:
every nontrivial zero ρ has 0 < Re ρ < 1, so |Re ρ − 1/2| < 1/2 ≤ α and the windowed zero
set `ZetaZerosInTraceStrip α` is the whole critical strip. Hence all four conjuncts of
`MasulloRH.trace_formula_rational` hold for every admissible test. -/
theorem trace_formula_rational_of_half_le (α : ℝ) (hα : 1 / 2 ≤ α) :
    ∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by sorry

end MasulloAudit
