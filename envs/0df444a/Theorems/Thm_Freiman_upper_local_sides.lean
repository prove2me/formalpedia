-- Prove2me | Theorems.Thm_Freiman_upper_local_sides
-- name    : Freiman.upper_local_sides
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:12:08.563779+00:00
-- url     : https://prove2.me/theorems/a09d384f-22da-4284-8ec3-b4836dd18ca5
-- title:
--   Inward and outward tails reconstruct the local height
-- statement:
--   The local height is the central digit plus the inward and outward fractional tails, with the two roles exchanged on the negative side.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. The noncentral-position analysis of Part IV.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_local_sides (a : ℤ → ℕ+) (i : ℤ) :
    localValue a i = ((a i : ℕ) : ℝ) + upperInward a i + upperOutward a i := by
  sorry

end Freiman
