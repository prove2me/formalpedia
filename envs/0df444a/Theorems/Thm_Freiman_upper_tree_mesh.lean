-- Prove2me | Theorems.Thm_Freiman_upper_tree_mesh
-- name    : Freiman.upper_tree_mesh
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:34.84322+00:00
-- url     : https://prove2.me/theorems/d90a9924-2215-405e-8a20-402cc3220eae
-- title:
--   The explicit restricted trees have vanishing mesh
-- statement:
--   The five-state trees shrink uniformly with their binary depth by prefix growth and the report’s Fibonacci cylinder estimate.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. Paragraph after m2a:ratio-table.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_mesh (p : List ℕ+) (k : Fin 5) :
    upperMesh (upperTree p k) := by
  sorry

end Freiman
