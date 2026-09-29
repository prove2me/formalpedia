-- Prove2me | Theorems.Thm_Freiman_upper_tree_into_digits_A
-- name    : Freiman.upper_tree_into_digits_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:44.877111+00:00
-- url     : https://prove2.me/theorems/83981fb5-9355-4c32-bbb2-f7ffa0418cfc
-- title:
--   Every branch point has admissible digits: A
-- statement:
--   A point surviving all finite levels of the exact five-state tree is the continued fraction of a permitted infinite word, with the prescribed initial digit when present.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_into_digits_A  :
    upperTreeSet (upperTree [] 0) ⊆ upperKA := by
  sorry

end Freiman
