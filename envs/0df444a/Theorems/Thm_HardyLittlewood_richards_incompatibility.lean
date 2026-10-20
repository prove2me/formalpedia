-- Prove2me | Theorems.Thm_HardyLittlewood_richards_incompatibility
-- name    : HardyLittlewood.richards_incompatibility
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-19T21:49:04.401997+00:00
-- url     : https://prove2.me/theorems/7106a6b5-100c-4e00-a48c-06746134a5b0
-- title:
--   Richards: the two Hardy–Littlewood conjectures are incompatible
-- statement:
--   Richards' theorem: the first Hardy–Littlewood conjecture, asserted for every tuple, and the second Hardy–Littlewood conjecture, asserted for every pair x, y ≥ 2, cannot both be true. The first conjecture produces, in a short interval, more primes than the subadditivity of the second conjecture permits. At most one of the two 1923 conjectures survives.
-- source:
--   Richards (1974), On the Incompatibility of Two Conjectures Concerning Primes, Bull. Amer. Math. Soc. 80, pp. 419-438; restated in Formal Conjectures (2025), HardyLittlewood.lean

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- Richards' incompatibility theorem: the first Hardy–Littlewood conjecture,
asserted for every tuple, and the second Hardy–Littlewood conjecture, asserted
for every pair x, y ≥ 2, cannot both be true. -/
theorem richards_incompatibility
    (h1 : ∀ (k : ℕ) (m : Fin k.succ → ℕ), firstHardyLittlewoodFor m)
    (h2 : ∀ (x y : ℕ), 2 ≤ x → 2 ≤ y → secondHardyLittlewoodFor x y) :
    False := by
  sorry

end HardyLittlewood
