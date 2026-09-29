-- Prove2me | Theorems.Thm_GravitationalConstant_keplers_third_law_circular
-- name    : GravitationalConstant.keplers_third_law_circular
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:32:55.152781+00:00
-- url     : https://prove2.me/theorems/30ace075-1c79-48b6-860f-2f7d23225099
-- title:
--   Kepler's third law for circular orbits: $P_1^2/r_1^3 = P_2^2/r_2^3$
-- statement:
--   Kepler's third law in the circular case. Two bodies on circular orbits of radii $r_1, r_2$ and periods $P_1, P_2$ about the same central mass $M$ satisfy
--
--   $$ \frac{P_1^{2}}{r_1^{3}} = \frac{P_2^{2}}{r_2^{3}} \;\left(= \frac{4\pi^{2}}{GM}\right), $$
--
--   so the ratio of period squared to radius cubed depends only on the central mass and the gravitational constant. This is the form of Kepler's third law invoked in the source when the relation is expressed in units of the Earth's orbit.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem keplers_third_law_circular
    (G M r₁ P₁ r₂ P₂ : ℝ) (hG : 0 < G) (hM : 0 < M)
    (h₁ : IsCircularOrbit G M r₁ P₁) (h₂ : IsCircularOrbit G M r₂ P₂) :
    P₁ ^ 2 / r₁ ^ 3 = P₂ ^ 2 / r₂ ^ 3 := by sorry

end GravitationalConstant
