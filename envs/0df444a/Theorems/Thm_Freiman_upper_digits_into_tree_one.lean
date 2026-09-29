-- Prove2me | Theorems.Thm_Freiman_upper_digits_into_tree_one
-- name    : Freiman.upper_digits_into_tree_one
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:47.72258+00:00
-- url     : https://prove2.me/theorems/4f16f72c-149f-40cd-9b4b-cd6609656ad9
-- title:
--   Admissible digits determine branches: one
-- statement:
--   Every continued fraction in the specified restricted set selects compatible intervals at every level of the exact five-row normal-deletion tree.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_digits_into_tree_one  :
    upperKOne ⊆ upperTreeSet (upperTree [1] 3) := by
  sorry

end Freiman
