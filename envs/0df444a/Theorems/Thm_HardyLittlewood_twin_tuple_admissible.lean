-- Prove2me | Theorems.Thm_HardyLittlewood_twin_tuple_admissible
-- name    : HardyLittlewood.twin_tuple_admissible
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:48:02.542263+00:00
-- url     : https://prove2.me/theorems/d7adc718-1a4c-44f7-b471-382b584ea21c
-- title:
--   The twin-prime configuration is admissible
-- statement:
--   The twin-prime offsets (0, 1) — giving the constellation (p, p + 2) — are admissible: the doubled offsets (0, 2) occupy at most two residue classes modulo any prime, so they never cover all classes. This is the concrete admissibility check that lets the first Hardy–Littlewood conjecture specialize to twin primes.
-- source:
--   Admissibility of the twin-prime pair (p, p + 2); Hardy and Littlewood (1923), Acta Math. 44, the twin-prime case of the prime k-tuple conjecture

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- The twin-prime configuration is admissible: the doubled offsets (0, 2)
occupy at most two residue classes modulo any prime, so they never cover all
residue classes. -/
theorem twin_tuple_admissible :
    IsAdmissibleTuple (![0, 1] : Fin 2 → ℕ) := by
  sorry

end HardyLittlewood
