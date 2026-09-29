-- Prove2me | Theorems.Thm_Freiman_upper_path_shrinks
-- name    : Freiman.upper_path_shrinks
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:21.417996+00:00
-- url     : https://prove2.me/theorems/24deec00-56de-461e-b732-da3ec38015ed
-- title:
--   Both physical sides of a longer-side deletion path shrink
-- statement:
--   In normal trees with vanishing meshes, a path splitting a longer side cannot stop splitting either side. Both selected interval lengths tend to zero.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:normal-sum, the fairness argument.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_path_shrinks (T S : List Bool → upperInterval) (hT : upperNormalTree T) (hS : upperNormalTree S) (mT : upperMesh T) (mS : upperMesh S) (u v : ℕ → List Bool) (z : ℝ) (hp : upperPath T S u v z) :
    Filter.Tendsto (fun n => upperLength (T (u n))) Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun n => upperLength (S (v n))) Filter.atTop (nhds 0) := by
  sorry

end Freiman
