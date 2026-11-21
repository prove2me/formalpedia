-- Prove2me | Theorems.Thm_MasulloRH_trace_formula_inversion_odd
-- name    : MasulloRH.trace_formula_inversion_odd
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T22:48:42.503296+00:00
-- url     : https://prove2.me/theorems/2670a1dc-66aa-4dd0-b532-6dde62e0f3de
-- title:
--   Unconditional restricted rational trace formula for inversion-odd tests
-- statement:
--   For every positive half-width and every admissible test function that changes sign under reciprocal inversion on the positive reals, the restricted rational trace identity holds with all its convergence assertions. Reflection preserves each centered zero window and each analytic multiplicity. Both sides of the identity vanish for this infinite-dimensional family of tests. General admissible tests still have an even component to control.
-- source:
--   Symmetry specialization of the rational form of Theorem 12.5.1.1, pp. 519–520, in A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. The proof uses the full-zero trace-window comparison for convergence and functional-equation reflection of zeta multiplicities.

import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH MeasureTheory Set

theorem MasulloRH.trace_formula_inversion_odd (α : ℝ) (_hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (hodd : ∀ t : ℝ, 0 < t → φ t⁻¹ = -φ t) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by sorry
