-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_akbulut_kirby
-- name    : HomologySpheresBoundBalls.hsbb_akbulut_kirby
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:19:32.356021+00:00
-- url     : https://prove2.me/theorems/a4d7cc9d-00f6-4339-b579-1fe07868cee4
-- title:
--   Akbulut–Kirby: $\Sigma(2,5,7)$, $\Sigma(3,4,5)$, $\Sigma(2,3,13)$ bound contractible 4-manifolds
-- statement:
--   Each of the Brieskorn homology spheres
--   $$\Sigma(2,5,7), \qquad \Sigma(3,4,5), \qquad \Sigma(2,3,13)$$
--   bounds a compact smooth contractible 4-manifold (a Mazur manifold). In particular each bounds a smooth integral homology 4-ball.
--
--   These were among the first Brieskorn spheres other than $S^3$ shown to bound contractible 4-manifolds.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- (Akbulut–Kirby) `Σ(2,5,7)`, `Σ(3,4,5)` and `Σ(2,3,13)` bound smooth contractible
4-manifolds (Mazur manifolds). -/
theorem hsbb_akbulut_kirby :
    BoundsContractible (BrieskornSphere 2 5 7) ∧
    BoundsContractible (BrieskornSphere 3 4 5) ∧
    BoundsContractible (BrieskornSphere 2 3 13) := by sorry

end HomologySpheresBoundBalls
