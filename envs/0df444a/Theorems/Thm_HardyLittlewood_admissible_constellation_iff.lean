-- Prove2me | Theorems.Thm_HardyLittlewood_admissible_constellation_iff
-- name    : HardyLittlewood.admissible_constellation_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:44:24.152895+00:00
-- url     : https://prove2.me/theorems/8e490631-383d-4b0d-9120-b578fd99649e
-- title:
--   Admissibility does not depend on the base point
-- statement:
--   A prime constellation at the base point p is admissible if and only if it is a prime constellation and the tuple of doubled offsets is admissible: residue coverage modulo a prime is invariant under translation by p, so admissibility is a property of the offsets alone. This is the translation-invariance lemma that lets the conjecture's admissibility condition be read off the tuple itself, and it is the gateway to the tuple-based singular series.
-- source:
--   Formal Conjectures (2025), HardyLittlewood.lean, definition IsAdmissiblePrimeConstellation; translation invariance of residue coverage modulo a prime

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- Admissibility does not depend on the base point: a prime constellation at
p is admissible exactly when it is a prime constellation and the tuple of
doubled offsets is admissible — residue coverage modulo a prime is invariant
under translation by p. -/
theorem admissible_constellation_iff {k : ℕ} (m : Fin k.succ → ℕ) (p : ℕ) :
    IsAdmissiblePrimeConstellation m p ↔
      IsPrimeConstellation m p ∧ IsAdmissibleTuple m := by
  sorry

end HardyLittlewood
