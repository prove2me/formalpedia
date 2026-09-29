-- Prove2me | Theorems.Thm_Freiman_upper_derived_diagonal
-- name    : Freiman.upper_derived_diagonal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:27.386978+00:00
-- url     : https://prove2.me/theorems/d0628f3b-b4ec-4b76-88a2-3de7b11b8974
-- title:
--   Equal initial intervals have a full derived sum interval
-- statement:
--   For a positive-length interval I, its two derived intervals with itself cover exactly the entire interval from twice its left endpoint to twice its right endpoint.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. The last paragraph of m2a:normal-sum, equal-length specialization.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_derived_diagonal (I : upperInterval) (hI : 0 < upperLength I) :
    upperDerived I I = Set.Icc (2 * I.left) (2 * I.right) := by
  sorry

end Freiman
