-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_rokhlin_poincare
-- name    : HomologySpheresBoundBalls.hsbb_rokhlin_poincare
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:17:37.217676+00:00
-- url     : https://prove2.me/theorems/040da2e0-d5af-4658-b8f7-8c1ecb6807da
-- title:
--   Rokhlin: the Poincaré sphere bounds no smooth integral homology ball
-- statement:
--   Let $P = \Sigma(2,3,5)$ be the Poincaré homology sphere. There is no compact smooth 4-manifold $W$ with boundary such that $H_n(W;\mathbb Z) \cong H_n(\mathrm{pt};\mathbb Z)$ for all $n$ and $\partial W$ is homeomorphic to $P$:
--   $$P \text{ does not bound a smooth integral homology 4-ball.}$$
--
--   The obstruction is the Rokhlin invariant, which is nontrivial for $P$. The statement is false in the topological category (Freedman), so smoothness of $W$ is essential.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- (Rokhlin) The Poincaré homology sphere does not bound a smooth integral homology 4-ball. -/
theorem hsbb_rokhlin_poincare : ¬ BoundsIntHomologyBall PoincareSphere := by sorry

end HomologySpheresBoundBalls
