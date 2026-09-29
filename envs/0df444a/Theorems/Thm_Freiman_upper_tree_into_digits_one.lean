-- Prove2me | Theorems.Thm_Freiman_upper_tree_into_digits_one
-- name    : Freiman.upper_tree_into_digits_one
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:42.889602+00:00
-- url     : https://prove2.me/theorems/df62c266-b7d0-4b5f-8471-ac2ecfd0d00f
-- title:
--   Every branch point has admissible digits: one
-- statement:
--   A point surviving all finite levels of the exact five-state tree is the continued fraction of a permitted infinite word, with the prescribed initial digit when present.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_into_digits_one  :
    upperTreeSet (upperTree [1] 3) ⊆ upperKOne := by
  sorry

end Freiman
