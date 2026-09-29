-- Prove2me | Theorems.Thm_Freiman_upper_deletion_both
-- name    : Freiman.upper_deletion_both
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:15.171651+00:00
-- url     : https://prove2.me/theorems/8aee5c02-f20e-49e6-be0d-350accdf8bf2
-- title:
--   One normal deletion: both
-- statement:
--   Both surviving intervals are at least as long as C. Under a normal deletion of the longer interval D, the two parent derived intervals are covered by the four child derived intervals.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:one-deletion, the corresponding length case.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_deletion_both (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) (hL : upperLength C ≤ upperLength L) (hR : upperLength C ≤ upperLength R) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  sorry

end Freiman
