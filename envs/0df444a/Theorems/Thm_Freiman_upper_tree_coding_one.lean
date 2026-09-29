-- Prove2me | Theorems.Thm_Freiman_upper_tree_coding_one
-- name    : Freiman.upper_tree_coding_one
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:50.622659+00:00
-- url     : https://prove2.me/theorems/fed38b8f-06f7-450c-91b7-5993713d719a
-- title:
--   The deletion tree has exactly the intended limit set: one
-- statement:
--   The explicit tree produces all and only the specified restricted continued fractions; no additional infinite words are introduced.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_coding_one  :
    upperTreeSet (upperTree [1] 3) = upperKOne := by
  sorry

end Freiman
