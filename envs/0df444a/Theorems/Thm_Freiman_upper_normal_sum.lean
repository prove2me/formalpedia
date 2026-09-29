-- Prove2me | Theorems.Thm_Freiman_upper_normal_sum
-- name    : Freiman.upper_normal_sum
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:18.277285+00:00
-- url     : https://prove2.me/theorems/ed39684f-b34f-4427-889b-04d882d9cbf0
-- title:
--   Normal-deletion sum theorem for the two derived intervals
-- statement:
--   For two normal deletion trees whose meshes tend to zero, both initial derived intervals are contained in the sum of the two limit sets.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:normal-sum.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_normal_sum (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (mT : upperMesh T) (mS : upperMesh S) :
    upperDerived (T []) (S []) ⊆ upperSumSet (upperTreeSet T) (upperTreeSet S) := by
  sorry

end Freiman
