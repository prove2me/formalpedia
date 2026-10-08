-- Prove2me | Theorems.Thm_NoHair_kerrNewman_einsteinMaxwell
-- name    : NoHair.kerrNewman_einsteinMaxwell
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-04T21:36:32.803051+00:00
-- url     : https://prove2.me/theorems/35932774-6f3d-4986-915d-e2e8baec247a
-- title:
--   Kerr–Newman metric solves the Einstein–Maxwell equations
-- statement:
--   For all real $m,a,e$ and every point $y$ of Kerr–Schild coordinate space with $r(y)>0$, the Kerr–Newman metric $g^{KN}_{m,a,e}=\eta+f\,k\otimes k$ and field $F^{KN}_{a,e}=dA$ satisfy at $y$
--   $$G_{\mu\nu}=2\Big(F_{\mu\alpha}F_\nu{}^\alpha-\tfrac14g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta}\Big),\qquad\partial_\mu\big(\sqrt{|\det g|}F^{\mu\nu}\big)=0,\qquad\partial_{[\lambda}F_{\mu\nu]}=0.$$
--
--   This confirms that the model family named in the no-hair theorem consists of solutions of the theory, in the conventions used throughout the mission.
-- source:
--   Wikipedia, "No-hair theorem" (revision oldid=1353599195), https://en.wikipedia.org/w/index.php?title=No-hair_theorem&oldid=1353599195

import Mathlib
import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold BigOperators
open Set Matrix

namespace NoHair

/-- **Milestone: Kerr–Newman solves Einstein–Maxwell.** In Kerr–Schild coordinates the
Kerr–Newman metric and field satisfy the Einstein–Maxwell equations wherever `r > 0`. -/
theorem kerrNewman_einsteinMaxwell (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    EinsteinMaxwellAt (kerrNewmanMetric m a e) (kerrNewmanField a e) y := by
  sorry

end NoHair
