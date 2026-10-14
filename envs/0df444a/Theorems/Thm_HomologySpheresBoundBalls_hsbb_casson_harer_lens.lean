-- Prove2me | Theorems.Thm_HomologySpheresBoundBalls_hsbb_casson_harer_lens
-- name    : HomologySpheresBoundBalls.hsbb_casson_harer_lens
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:20:42.598554+00:00
-- url     : https://prove2.me/theorems/011d0dca-1646-4430-a2ad-c8d79c7976e0
-- title:
--   Casson–Harer: $L(m^2, mk-1)$ bounds a rational homology ball
-- statement:
--   Let $m, k$ be natural numbers with $0 < k < m$ and $\gcd(m,k) = 1$. Then the lens space
--   $$L(m^2,\ mk-1)$$
--   bounds a compact smooth rational homology 4-ball.
--
--   This is the family of lens spaces in the title of Casson–Harer's paper; Lisca later classified all sums of lens spaces bounding rational balls.
-- source:
--   Open Problem Garden, 'Which homology 3-spheres bound homology 4-balls?' (rybu, 2009), http://www.openproblemgarden.org/op/which_homology_3_spheres_bound_homology_4_balls

import Definitions.Def_hsbb_homology_balls
import Definitions.Def_hsbb_spaces

open scoped Manifold

namespace HomologySpheresBoundBalls

/-- (Casson–Harer) For coprime `0 < k < m`, the lens space `L(m², mk - 1)` bounds a smooth
rational homology 4-ball. -/
theorem hsbb_casson_harer_lens (m k : ℕ) (hk : 0 < k) (hkm : k < m) (hcop : Nat.Coprime m k) :
    BoundsRatHomologyBall (LensSpace (m ^ 2) (m * k - 1)) := by sorry

end HomologySpheresBoundBalls
