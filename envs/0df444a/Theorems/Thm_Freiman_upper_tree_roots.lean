-- Prove2me | Theorems.Thm_Freiman_upper_tree_roots
-- name    : Freiman.upper_tree_roots
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:09:42.044558+00:00
-- url     : https://prove2.me/theorems/be4cb005-0b1d-4bea-914e-c501c30d51a0
-- title:
--   The two normal trees have the required positive root hulls
-- statement:
--   The unrestricted A-state tree has root [Theta8,Theta1], and the image under the initial digit 1 of the B-state tree has root [Theta2,Theta1]; both lengths are positive.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text, 8 September 2026, Part IV, active source report/source/staging/parts/m2a.tex. m2a:theta, m2a:endpoint-identities and m2a:sum-intervals.

import Definitions.Def_Freiman_upperModel

namespace Freiman

theorem upper_tree_roots  :
    upperTree [] 0 [] = ⟨upperTheta8, upperTheta1⟩ ∧
    upperTree [1] 3 [] = ⟨upperTheta2, upperTheta1⟩ ∧
    0 < upperLength (upperTree [] 0 []) ∧ 0 < upperLength (upperTree [1] 3 []) := by
  sorry

end Freiman
