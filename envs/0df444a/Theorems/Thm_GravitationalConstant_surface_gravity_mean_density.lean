-- Prove2me | Theorems.Thm_GravitationalConstant_surface_gravity_mean_density
-- name    : GravitationalConstant.surface_gravity_mean_density
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:27:20.164111+00:00
-- url     : https://prove2.me/theorems/bbc03576-16d9-4fdb-9609-139ebe0b7d4a
-- title:
--   Mean-density form of surface gravity: $g = \tfrac{4}{3}\pi G \rho R$
-- statement:
--   Measuring the mean density of a body is equivalent to measuring $G$. For a body of mass $M$ filling a ball of radius $R>0$, with mean density $\rho = M/(\tfrac{4}{3}\pi R^3)$, the surface gravity satisfies
--
--   $$ g = \frac{GM}{R^{2}} = \frac{4}{3}\pi G \rho R. $$
--
--   This is the identity behind the Schiehallion experiment and the Cavendish experiment: given the Earth's mean radius and the measured surface acceleration, a determination of the mean density is a determination of $G$.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem surface_gravity_mean_density
    (G M R : ℝ) (hR : 0 < R) :
    surfaceGravity G M R = 4 / 3 * Real.pi * G * meanDensity M R * R := by sorry

end GravitationalConstant
