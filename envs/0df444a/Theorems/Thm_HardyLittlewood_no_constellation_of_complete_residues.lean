-- Prove2me | Theorems.Thm_HardyLittlewood_no_constellation_of_complete_residues
-- name    : HardyLittlewood.no_constellation_of_complete_residues
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-19T21:45:08.005749+00:00
-- url     : https://prove2.me/theorems/3696a205-3518-43d5-b339-870642f0b3bc
-- title:
--   Complete residue coverage kills prime constellations
-- statement:
--   Necessity of admissibility: if the residues of the constellation entries p + 2m_i cover all classes modulo a prime q with q < p, then the entries cannot all be prime — one of them is a positive multiple of q strictly larger than q. A prime constellation at p therefore forces its residue coverage to miss a class modulo every prime smaller than p.
-- source:
--   Hardy and Littlewood (1923), Acta Math. 44, the admissibility condition for prime tuples; Formal Conjectures (2025), HardyLittlewood.lean, definition IsPrimeConstellation

import Mathlib
import Definitions.Def_HardyLittlewood_constellation
import Definitions.Def_HardyLittlewood_counting
import Definitions.Def_HardyLittlewood_series

namespace HardyLittlewood

/-- Necessity of admissibility, locally: if the residues of the constellation
entries p + 2·m i cover all of ZMod q for a prime q smaller than p, then the
entries cannot all be prime — one of them is a positive multiple of q
strictly larger than q. -/
theorem no_constellation_of_complete_residues {k : ℕ} (m : Fin k.succ → ℕ)
    (q p : ℕ) (hq : q.Prime) (hqp : q < p)
    (h : Function.Surjective (fun i : Fin k.succ => (p + 2 * m i : ZMod q))) :
    ¬ IsPrimeConstellation m p := by
  sorry

end HardyLittlewood
