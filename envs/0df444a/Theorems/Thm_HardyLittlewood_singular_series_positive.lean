-- Prove2me | Theorems.Thm_HardyLittlewood_singular_series_positive
-- name    : HardyLittlewood.singular_series_positive
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:46:36.446123+00:00
-- url     : https://prove2.me/theorems/e4159d94-046d-405d-b0ba-0d7747638e65
-- title:
--   The singular series of an admissible tuple is positive
-- statement:
--   For a tuple of pairwise distinct offsets that is admissible — the doubled offsets miss a residue class modulo every prime — the singular series constant C_P is a strictly positive real number: the Euler product over the odd primes converges to a positive limit, since all but finitely many of its factors are 1 + O(1/q²) and every factor is positive. Positivity is what turns the conjecture's asymptotic into an infinitude.
-- source:
--   Hardy and Littlewood (1923), Acta Math. 44, the singular series of the prime k-tuple conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The singular series of an admissible tuple of distinct offsets is a
well-defined positive constant: for injective m whose doubled offsets miss a
residue class modulo every prime, the Euler product over the odd primes
converges to a strictly positive value. -/
theorem singular_series_positive {k : ℕ} (m : Fin k.succ → ℕ)
    (hinj : Function.Injective m) (hadm : IsAdmissibleTuple m) :
    0 < singularSeriesConstant m := by
  sorry

end HardyLittlewood
