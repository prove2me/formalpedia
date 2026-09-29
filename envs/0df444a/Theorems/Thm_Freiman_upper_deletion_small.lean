-- Prove2me | Theorems.Thm_Freiman_upper_deletion_small
-- name    : Freiman.upper_deletion_small
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:18.0131+00:00
-- url     : https://prove2.me/theorems/063bebd2-d8c4-47c9-8918-ec811a580af8
-- title:
--   One normal deletion: small
-- statement:
--   Both surviving intervals are shorter than C; their four derived intervals form a connected union. Under a normal deletion of the longer interval D, the two parent derived intervals are covered by the four child derived intervals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:one-deletion, the corresponding length case.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_deletion_small (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) (hL : upperLength L < upperLength C) (hR : upperLength R < upperLength C) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  sorry

end Freiman
