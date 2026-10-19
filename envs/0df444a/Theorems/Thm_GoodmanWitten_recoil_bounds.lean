-- Prove2me | Theorems.Thm_GoodmanWitten_recoil_bounds
-- name    : GoodmanWitten.recoil_bounds
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T12:50:58.161708+00:00
-- url     : https://prove2.me/theorems/d085aa1e-2a86-49f9-8a4a-497a0960cfd7
-- title:
--   Recoil momentum and energy bounds for elastic halo-particle scattering
-- statement:
--   Consider a non-relativistic elastic collision in $\mathbb R^3$ between a halo particle of mass $m>0$ with initial velocity $u$ and a nucleus of mass $M>0$ initially at rest. Let $u'$ and $V$ be the velocities of the particle and of the nucleus after the collision, so that momentum and kinetic energy are conserved:
--   $$
--   m u = m u' + M V,\qquad \tfrac12 m|u|^2 = \tfrac12 m|u'|^2 + \tfrac12 M|V|^2 .
--   $$
--   Then the recoil momentum and recoil kinetic energy of the nucleus satisfy
--   $$
--   |MV| \le 2m|u|,\qquad \tfrac12 M|V|^2 \le \frac{(2m|u|)^2}{2M}.
--   $$
--
--   These bounds give the largest energy a halo particle can deposit in a detector nucleus and are the basis of the paper's lower limit on detectable masses.
-- source:
--   M. W. Goodman and E. Witten, Detectability of certain dark-matter candidates, Phys. Rev. D 31, 3059-3063 (1985), https://doi.org/10.1103/PhysRevD.31.3059, p. 3059, right column, paragraph 2

import Mathlib
import Definitions.Def_GoodmanWitten_basic

namespace GoodmanWitten

theorem recoil_bounds (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (u u' V : EuclideanSpace ℝ (Fin 3))
    (hmom : m • u = m • u' + M • V)
    (hen : m / 2 * ‖u‖ ^ 2 = m / 2 * ‖u'‖ ^ 2 + M / 2 * ‖V‖ ^ 2) :
    ‖M • V‖ ≤ maxRecoilMomentum m ‖u‖ ∧
      M / 2 * ‖V‖ ^ 2 ≤ maxRecoilEnergy m M ‖u‖ := by sorry

end GoodmanWitten
