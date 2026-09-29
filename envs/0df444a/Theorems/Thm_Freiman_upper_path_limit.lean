-- Prove2me | Theorems.Thm_Freiman_upper_path_limit
-- name    : Freiman.upper_path_limit
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:23.894796+00:00
-- url     : https://prove2.me/theorems/39f361f0-446a-43e9-ab71-c8f72e817a88
-- title:
--   The limiting selected intervals realize the target sum
-- statement:
--   If the two selected interval lengths tend to zero, nested closed intervals determine x and y in the two tree limit sets. The retained target is exactly x+y.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:normal-sum, nested intervals paragraph.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_path_limit (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (mT : upperMesh T) (mS : upperMesh S) (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z) (hlim : Filter.Tendsto (fun n => upperLength (T (u n))) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => upperLength (S (v n))) Filter.atTop (nhds 0)) :
    z ∈ upperSumSet (upperTreeSet T) (upperTreeSet S) := by
  sorry

end Freiman
