-- Prove2me | Theorems.Thm_HardyLittlewood_first_hardy_littlewood
-- name    : HardyLittlewood.first_hardy_littlewood
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T21:49:26.141358+00:00
-- url     : https://prove2.me/theorems/207bff75-ab7c-4d48-b7da-b72e45ce4724
-- title:
--   The first Hardy–Littlewood conjecture: prime constellations have logarithmic-integral density
-- statement:
--   The goal: for every tuple m with m₀ = 0 and pairwise distinct offsets, the counting function π_P(n) of admissible prime constellations with offsets m is asymptotic to C_P times the integral of 1/(log t)^(k+1) from 2 to n, where C_P is the singular series constant of the tuple. For the twin offsets this yields the twin prime conjecture; in general it is the prime k-tuple conjecture of 1923, the open heart of the mission.
-- source:
--   Hardy and Littlewood (1923), Some problems of 'Partitio numerorum'; III, Acta Math. 44, pp. 1-70, the prime k-tuple conjecture; Formal Conjectures (2025), HardyLittlewood.lean, theorem first_hardy_littlewood_conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The first Hardy–Littlewood conjecture: for every tuple m with m 0 = 0 and
pairwise distinct offsets, the counting function π_P(n) of admissible prime
constellations with offsets m and base point at most n is asymptotic to the
singular series constant C_P times the (k+1)-fold logarithmic integral from 2
to n. -/
theorem first_hardy_littlewood {k : ℕ} (m : Fin k.succ → ℕ) :
    firstHardyLittlewoodFor m := by
  sorry

end HardyLittlewood
