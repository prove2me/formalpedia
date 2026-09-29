-- Prove2me | Theorems.Thm_GrothendieckTeichmuller_mzv_euler_two_one
-- name    : GrothendieckTeichmuller.mzv_euler_two_one
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T21:55:39.642019+00:00
-- url     : https://prove2.me/theorems/95a97589-6cfd-4af3-af97-82a0a1801e68
-- title:
--   Euler's identity $\zeta(2,1) = \zeta(3)$
-- statement:
--   Euler's identity for the double zeta value of weight three:
--
--   $$\zeta(2,1) \;=\; \sum_{j_1 > j_2 \ge 1} \frac{1}{j_1^{2}\, j_2} \;=\; \sum_{j \ge 1}\frac{1}{j^3} \;=\; \zeta(3).$$
--
--   The source cites it as the simplest relation among multiple zeta values that is *not* a consequence of the double shuffle relations of Section 6.1, motivating their regularized extension in Section 6.2. Here it also serves as a concrete check on the definition of the multiple zeta value used throughout this mission.
-- source:
--   Thomas Willwacher, The Grothendieck-Teichmüller Group, ETH Zürich lecture notes (in progress), 27 February 2014, Section 6.1, p. 53 (definition of multiple zeta values, stuffle product, Proposition 6.1, shuffle product, Proposition 6.2, Euler's identity zeta(2,1) = zeta(3)) (the displayed identity zeta(2,1) = zeta(3) given as the simplest relation not implied by the double shuffle relations)

import Definitions.Def_GT_multizeta

namespace GrothendieckTeichmuller

theorem mzv_euler_two_one : mzv [2, 1] = mzv [3] := by sorry

end GrothendieckTeichmuller
