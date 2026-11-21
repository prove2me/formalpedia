-- Prove2me | Theorems.Thm_MasulloRH_primePowerTraceTerm_finite_support
-- name    : MasulloRH.primePowerTraceTerm_finite_support
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:16:20.481985+00:00
-- url     : https://prove2.me/theorems/696299e4-c85f-4090-99f2-7fe0009a6426
-- title:
--   Finite support of the rational prime-power trace
-- statement:
--   Only finitely many pairs of a prime and a positive exponent contribute to the rational finite-place trace. Both prime powers and their reciprocals are evaluated against the same test function with compact support inside the positive reals.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Theorem 12.5.1.1, pp. 519–520. Component of the mission’s rational specialization MasulloRH.trace_formula_rational. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace

open MeasureTheory Set

namespace MasulloRH

theorem primePowerTraceTerm_finite_support (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    (Function.support (primePowerTraceTerm φ)).Finite := by sorry

end MasulloRH
