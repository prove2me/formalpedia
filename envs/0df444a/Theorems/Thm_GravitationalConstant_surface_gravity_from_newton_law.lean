-- Prove2me | Theorems.Thm_GravitationalConstant_surface_gravity_from_newton_law
-- name    : GravitationalConstant.surface_gravity_from_newton_law
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:22:56.236982+00:00
-- url     : https://prove2.me/theorems/f54825ea-64f5-4326-b841-fd4eaea2d3c2
-- title:
--   Big $G$ and small $g$: force per unit test mass is $GM/R^2$
-- statement:
--   The relation between "big $G$" and "small $g$". The Newtonian attraction exerted by a body of mass $M$ on a test mass $m$ whose centre is a distance $R$ away is $F = GMm/R^2$; dividing by the test mass gives the local gravitational field strength
--
--   $$ \frac{F}{m} = \frac{G M}{R^{2}} = g, $$
--
--   for any nonzero test mass $m$. This is the identity that lets a measurement of the free-fall acceleration at the surface of a body stand in for a measurement of $GM$.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem surface_gravity_from_newton_law
    (G M m R : ℝ) (hm : m ≠ 0) :
    newtonForce G M m R / m = surfaceGravity G M R := by sorry

end GravitationalConstant
