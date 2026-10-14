-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_poincare_double_bounds
-- name    : HomologySpheresBoundBalls.hsbb_poincare_double_bounds
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:18:16.944425+00:00
-- url     : https://prove2.me/theorems/eaa07af0-7ccc-4c08-b4e9-0de55cffe705
-- title:
--   $P \# (-P)$ bounds a smooth integral homology ball
-- statement:
--   Equip the Poincaré homology sphere $P = \Sigma(2,3,5)$ with any atlas modelled on $\mathbb R^3$ (compatible with its topology). Let $x \in P$, $r > 0$, and let $\varphi$ be the chart at $x$, with the closed ball $\overline{B}(\varphi x, r)$ contained in the chart's target. Let $B = \varphi^{-1}(B(\varphi x, r))$. Then the double
--   $$D(P \setminus B) \;\cong\; P \# (-P)$$
--   bounds a smooth integral homology 4-ball.
--
--   This shows that the obstruction in the previous milestone does not survive connected sum with the orientation reverse, illustrating that bounding is a group-theoretic question in homology cobordism.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- `P # (-P)`, realized as the double of `P` minus an open chart ball, bounds a smooth
integral homology 4-ball (namely `(P ∖ B) × [0,1]`). -/
theorem hsbb_poincare_double_bounds [ChartedSpace (EuclideanSpace ℝ (Fin 3)) PoincareSphere]
    (x : PoincareSphere) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (chartAt (EuclideanSpace ℝ (Fin 3)) x x) r ⊆
      (chartAt (EuclideanSpace ℝ (Fin 3)) x).target) :
    BoundsIntHomologyBall (PuncturedDouble x r) := by sorry

end HomologySpheresBoundBalls
