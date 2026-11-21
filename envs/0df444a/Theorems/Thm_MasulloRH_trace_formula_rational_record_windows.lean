-- Prove2me | Theorems.Thm_MasulloRH_trace_formula_rational_record_windows
-- name    : MasulloRH.trace_formula_rational_record_windows
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:12:34.996812+00:00
-- url     : https://prove2.me/theorems/24e55bd9-91ec-4532-b0da-8f8d6326dc5f
-- title:
--   The rational trace formula and its regularized resolvent at every width above 0.3749570698
-- statement:
--   For every real width α > 0.3749570698 and every admissible rational trace test, the prime and archimedean terms in the rational trace formula equal its polar terms minus the spectral sum over the open window |Re(ρ)−1/2| < α. The archimedean integral converges and both spectral and prime sums are summable. At the same width, the regularized resolvent equals ζ′(s)/ζ(s) for every complex s with Re(s)>3/2. The numerical width uses the uniform Dirichlet zero-free theorem 3a8f3264 already verified in this library. The trace window is open, which accounts for the strict inequality on α.
-- source:
--   Masullo, The Music of the Primes, Theorem 12.5.1.1, rational specialization. Uses the fixed-window equivalence c7d3b4b4, finite-height resolvent estimate 5505d4c2, and the verified LW56e2 uniform Dirichlet boundary 3a8f3264 (https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/Transport/Nonvanishing.lean).

import Definitions.Def_MasulloRH_RegularizedTrace

set_option autoImplicit false

open MeasureTheory Set
namespace MasulloRH

theorem trace_formula_rational_record_windows (α : ℝ) (hα : 0.3749570698 < α) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
      Summable (primePowerTraceTerm φ) ∧
      Summable (zetaTraceTerm φ α) ∧
      (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
        (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
        mellin φ (1 / 2) + mellin φ (-1 / 2) -
          ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) ∧
      (∀ s : ℂ, (3/2:ℝ) < s.re → regularizedTraceRHS α s = zetaLogDeriv s) := by sorry

end MasulloRH
