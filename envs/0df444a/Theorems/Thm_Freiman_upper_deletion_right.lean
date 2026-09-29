-- Prove2me | Theorems.Thm_Freiman_upper_deletion_right
-- name    : Freiman.upper_deletion_right
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:17.615434+00:00
-- url     : https://prove2.me/theorems/35bbb5fd-8d25-422d-a212-8f53ab94b830
-- title:
--   One normal deletion: right
-- statement:
--   The right surviving interval is at least as long as C and the left one is shorter. Under a normal deletion of the longer interval D, the two parent derived intervals are covered by the four child derived intervals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:one-deletion, the corresponding length case.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_deletion_right (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) (hL : upperLength L < upperLength C) (hR : upperLength C ≤ upperLength R) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  sorry

end Freiman
