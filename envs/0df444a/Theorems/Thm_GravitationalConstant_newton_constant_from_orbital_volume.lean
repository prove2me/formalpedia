-- Prove2me | Theorems.Thm_GravitationalConstant_newton_constant_from_orbital_volume
-- name    : GravitationalConstant.newton_constant_from_orbital_volume
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:15:55.679616+00:00
-- url     : https://prove2.me/theorems/783ec71c-d4e9-49eb-8251-635d577deba4
-- title:
--   $G = 3\pi V / (P^2 M)$ from a circular orbit
-- statement:
--   **Goal theorem.** Let $G>0$ be a gravitational constant and $M>0$ a mass, and let a body move on a circular orbit of radius $r$ and period $P$ about $M$, meaning $r>0$, $P>0$ and $(2\pi/P)^2 r = GM/r^2$. Write $V = \tfrac{4}{3}\pi r^3$ for the volume enclosed by the orbit. Then
--
--   $$ G = \frac{3\pi V}{P^2 M}. $$
--
--   In words: the gravitational constant is determined by the period of a circular orbit, the volume that orbit encloses, and the total mass inside it. This is the form of the relation the source uses to connect $G$ to the mean density of a planet and the period of a satellite skimming its surface.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem newton_constant_from_orbital_volume
    (G M r P : ℝ) (hG : 0 < G) (hM : 0 < M) (horb : IsCircularOrbit G M r P) :
    G = 3 * Real.pi * ballVolume r / (P ^ 2 * M) := by sorry

end GravitationalConstant
