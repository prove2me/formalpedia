-- Prove2me | Theorems.Thm_GravitationalConstant_gravitational_constant_si_eq_cgs
-- name    : GravitationalConstant.gravitational_constant_si_eq_cgs
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T14:02:14.092746+00:00
-- url     : https://prove2.me/theorems/9345fc83-0e55-4ca3-b46d-7149baf15a7d
-- title:
--   SI and cgs values of $G$ agree: $6.674\,30\times10^{-11}\,\mathrm{m^3 kg^{-1} s^{-2}} = 6.674\,30\times10^{-8}\,\mathrm{dyn\,cm^2 g^{-2}}$
-- statement:
--   The two numerical values of $G$ quoted by the source,
--
--   $$ 6.674\,30\times10^{-11}\ \mathrm{m^{3}\,kg^{-1}\,s^{-2}} \qquad\text{and}\qquad 6.674\,30\times10^{-8}\ \mathrm{dyn\,cm^{2}\,g^{-2}}, $$
--
--   denote the same physical quantity. Modelling each unit symbol as a real scale factor and imposing the defining relations between the systems - $1\,\mathrm{m} = 100\,\mathrm{cm}$, $1\,\mathrm{kg} = 1000\,\mathrm{g}$, $1\,\mathrm{dyn} = 1\,\mathrm{g\,cm\,s^{-2}}$ - the two expressions are equal.
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem gravitational_constant_si_eq_cgs
    (metre kilogram second centimetre gram dyne : ℝ)
    (hcm : metre = 100 * centimetre) (hg : kilogram = 1000 * gram)
    (hdyn : dyne = gram * centimetre / second ^ 2)
    (hcm0 : centimetre ≠ 0) (hg0 : gram ≠ 0) (hs0 : second ≠ 0) :
    gravitationalConstantSI * (metre ^ 3 / (kilogram * second ^ 2)) =
      6.67430e-8 * (dyne * centimetre ^ 2 / gram ^ 2) := by sorry

end GravitationalConstant
