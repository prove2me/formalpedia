-- Prove2me | Theorems.Thm_OAI_TriangularCovering_rough_angle
-- name    : OAI.TriangularCovering.rough_angle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T18:45:52.510829+00:00
-- url     : https://prove2.me/theorems/73e08ff3-6882-4656-b512-7d96ceb19d60
-- title:
--   First-order estimate $|y-q/2|\le\varepsilon$ for a perturbed radial relation
-- statement:
--   Let $\varepsilon\ge0$ and let $x,q,a,r,y$ be real numbers with
--   $$
--   |x|\le1,\qquad |q|\le1,\qquad |a|\le\frac12,\qquad \frac12\le r\le\frac12+\frac{\varepsilon}{2},\qquad y=rq+\varepsilon xa .
--   $$
--   Then
--   $$
--   \left|y-\frac q2\right|\le\varepsilon .
--   $$
--
--   In the covering of the tetrahedron by tilted triangular cylinders, $r$ is a radial coordinate, $q$ an angular coordinate and $a$ a tilt coefficient, related to the cartesian coordinate $y$ by $y=rq+\varepsilon xa$. The lemma is a crude first-order estimate: once the radial coordinate is known to lie in $[\frac12,\frac12+\frac\varepsilon2]$, the value $q/2$ approximates $y$ within $\varepsilon$. It is used in the proof of the radial exclusion estimate, in the regime where both cutoffs fail.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean#L131-L150

import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem OAI.TriangularCovering.rough_angle {ε x y q a r : ℝ} (he : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1 / 2)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε / 2)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ ε := by sorry
