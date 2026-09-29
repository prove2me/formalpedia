-- Prove2me | Theorems.Thm_Freiman_upper_one_deletion
-- name    : Freiman.upper_one_deletion
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:22.437299+00:00
-- url     : https://prove2.me/theorems/711ffb4a-c293-4e20-b51b-fb4fe44564d7
-- title:
--   One normal deletion preserves the target intervals
-- statement:
--   If C is no longer than D and D is split normally, every target in the union of the two parent derived intervals remains in a derived interval for one surviving child.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:one-deletion.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_one_deletion (C D L R : upperInterval) (hC : 0 < upperLength C) (hCD : upperLength C ≤ upperLength D) (hs : upperNormalSplit D L R) :
    upperDerived C D ⊆ upperDerived C L ∪ upperDerived C R := by
  sorry

end Freiman
