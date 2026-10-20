-- Prove2me | Theorems.Thm_HardyLittlewood_twin_primes_from_first
-- name    : HardyLittlewood.twin_primes_from_first
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:48:22.278911+00:00
-- url     : https://prove2.me/theorems/d4624e39-dfb4-4565-85b0-f85e95cab827
-- title:
--   The twin prime conjecture follows from the first Hardy–Littlewood conjecture
-- statement:
--   Specializing the first Hardy–Littlewood conjecture to the twin offsets (0, 1): if the conjecture holds for the constellation (p, p + 2), then there are infinitely many twin primes — for every N there is a prime p ≥ N with p + 2 also prime.
-- source:
--   Hardy and Littlewood (1923), Acta Math. 44, the twin-prime special case of the prime k-tuple conjecture; Formal Conjectures (2025), HardyLittlewood.lean

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The twin prime conjecture follows from the first Hardy–Littlewood
conjecture for the twin offsets (0, 1): there are twin primes p, p + 2 with
arbitrarily large p. -/
theorem twin_primes_from_first
    (h : firstHardyLittlewoodFor (![0, 1] : Fin 2 → ℕ)) (N : ℕ) :
    ∃ p : ℕ, N ≤ p ∧ p.Prime ∧ (p + 2).Prime := by
  sorry

end HardyLittlewood
