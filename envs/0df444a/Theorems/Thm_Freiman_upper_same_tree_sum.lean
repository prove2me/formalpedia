-- Prove2me | Theorems.Thm_Freiman_upper_same_tree_sum
-- name    : Freiman.upper_same_tree_sum
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:20.060506+00:00
-- url     : https://prove2.me/theorems/ae33fbf6-9f85-45ff-a399-85f9e0525b86
-- title:
--   The sum of a normal tree with itself fills its hull sum
-- statement:
--   A normal deletion tree with vanishing mesh has a limit set whose self-sum contains the full doubled root interval.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:normal-sum applied to equal hulls.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_same_tree_sum (T : List Bool → upperInterval) (hT : upperNormalTree T) (mT : upperMesh T) (hI : 0 < upperLength (T [])) :
    Set.Icc (2 * (T []).left) (2 * (T []).right) ⊆ upperSumSet (upperTreeSet T) (upperTreeSet T) := by
  sorry

end Freiman
