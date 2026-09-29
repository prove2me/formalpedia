-- Prove2me | Theorems.Thm_Freiman_upper_digits_into_tree_A
-- name    : Freiman.upper_digits_into_tree_A
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:37.454262+00:00
-- url     : https://prove2.me/theorems/4e8cc6c1-c600-4c27-8959-97683428388b
-- title:
--   Admissible digits determine branches: A
-- statement:
--   Every continued fraction in the specified restricted set selects compatible intervals at every level of the exact five-row normal-deletion tree.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Exact tree coding following m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_digits_into_tree_A  :
    upperKA ⊆ upperTreeSet (upperTree [] 0) := by
  sorry

end Freiman
