-- Prove2me | Theorems.Thm_Freiman_upper_deletion_left
-- name    : Freiman.upper_deletion_left
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:08.917852+00:00
-- url     : https://prove2.me/theorems/4f3789f3-4a4b-458f-bad7-a771e3b10736
-- title:
--   One normal deletion: left
-- statement:
--   The left surviving interval is at least as long as C and the right one is shorter. Under a normal deletion of the longer interval D, the two parent derived intervals are covered by the four child derived intervals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:one-deletion, the corresponding length case.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_deletion_left (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) (hL : upperLength C ≤ upperLength L) (hR : upperLength R < upperLength C) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  sorry

end Freiman
