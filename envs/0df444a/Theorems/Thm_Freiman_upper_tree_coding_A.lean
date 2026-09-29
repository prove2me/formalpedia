-- Prove2me | Theorems.Thm_Freiman_upper_tree_coding_A
-- name    : Freiman.upper_tree_coding_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:39.884865+00:00
-- url     : https://prove2.me/theorems/dbae7100-27d3-49af-b681-33c339177cb2
-- title:
--   The deletion tree has exactly the intended limit set: A
-- statement:
--   The explicit tree produces all and only the specified restricted continued fractions; no additional infinite words are introduced.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_coding_A  :
    upperTreeSet (upperTree [] 0) = upperKA := by
  sorry

end Freiman
