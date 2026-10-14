-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_fintushel_stern
-- name    : HomologySpheresBoundBalls.hsbb_fintushel_stern
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:21:03.092837+00:00
-- url     : https://prove2.me/theorems/f64fc3f7-22e0-4140-be60-036dcbfda7de
-- title:
--   Fintushel–Stern: $\Sigma(2,3,7)$ bounds a rational homology ball
-- statement:
--   The Brieskorn homology sphere
--   $$\Sigma(2,3,7) = \{ z \in \mathbb C^3 : z_0^2 + z_1^3 + z_2^7 = 0,\ \|z\| = 1 \}$$
--   bounds a compact smooth rational homology 4-ball.
--
--   Its Rokhlin invariant is nontrivial, so it bounds no integral homology ball; this example separates the rational and integral versions of the question.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- (Fintushel–Stern) The Brieskorn sphere `Σ(2,3,7)` bounds a smooth rational homology 4-ball. -/
theorem hsbb_fintushel_stern : BoundsRatHomologyBall (BrieskornSphere 2 3 7) := by sorry

end HomologySpheresBoundBalls
