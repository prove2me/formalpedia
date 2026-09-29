-- Prove2me | Theorems.Thm_GravitationalConstant_grazing_orbit_period_mean_density
-- name    : GravitationalConstant.grazing_orbit_period_mean_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:43:23.388887+00:00
-- url     : https://prove2.me/theorems/9fd708a0-0430-4d98-b75a-293a4261b687
-- title:
--   Grazing satellite: $P^2 = 3\pi/(G\rho)$
-- statement:
--   A satellite on a circular orbit at the surface radius $R$ of a body of mass $M$ and mean density $\rho = M/(\tfrac{4}{3}\pi R^3)$ has period
--
--   $$ P^{2} = \frac{3\pi}{G\rho}. $$
--
--   The size of the body has dropped out: the period of a satellite orbiting just above the surface depends only on the body's average density. This is the source's statement of the relationship between the average density of a planet and the period of such a satellite.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem grazing_orbit_period_mean_density
    (G M R P : ℝ) (hG : 0 < G) (hM : 0 < M) (horb : IsCircularOrbit G M R P) :
    P ^ 2 = 3 * Real.pi / (G * meanDensity M R) := by sorry

end GravitationalConstant
