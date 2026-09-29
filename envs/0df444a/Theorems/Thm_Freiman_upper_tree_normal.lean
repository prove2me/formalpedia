-- Prove2me | Theorems.Thm_Freiman_upper_tree_normal
-- name    : Freiman.upper_tree_normal
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:36.091763+00:00
-- url     : https://prove2.me/theorems/2c596109-eca7-4063-872c-955a20e07c83
-- title:
--   The explicit restricted continued-fraction trees are normal
-- statement:
--   Every node of the explicitly defined five-state deletion tree has a normal physical split.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Binary deletion order and m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_normal (p : List ℕ+) (k : Fin 5) :
    upperNormalTree (upperTree p k) := by
  sorry

end Freiman
