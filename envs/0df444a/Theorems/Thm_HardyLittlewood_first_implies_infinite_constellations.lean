-- Prove2me | Theorems.Thm_HardyLittlewood_first_implies_infinite_constellations
-- name    : HardyLittlewood.first_implies_infinite_constellations
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:47:19.89888+00:00
-- url     : https://prove2.me/theorems/5bdbefc4-3683-443e-825e-47f17fd1171a
-- title:
--   The conjecture yields infinitely many prime constellations
-- statement:
--   For an admissible tuple of distinct offsets with m₀ = 0, the first Hardy–Littlewood conjecture implies that prime constellations with those offsets occur at arbitrarily large base points: for every N there is a base point p ≥ N whose constellation (p, p + 2m₁, ..., p + 2m_k) consists entirely of primes. The derivation runs through the positivity of the singular series and the divergence of the model integral.
-- source:
--   Consequence of Hardy and Littlewood (1923), Acta Math. 44, the prime k-tuple conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The infinitude consequence: for an admissible tuple of distinct offsets
with m 0 = 0, the first Hardy–Littlewood conjecture implies that prime
constellations with those offsets occur at arbitrarily large base points. -/
theorem first_implies_infinite_constellations {k : ℕ} (m : Fin k.succ → ℕ)
    (hm0 : m 0 = 0) (hinj : Function.Injective m) (hadm : IsAdmissibleTuple m)
    (h : firstHardyLittlewoodFor m) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ IsPrimeConstellation m p := by
  sorry

end HardyLittlewood
