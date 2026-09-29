-- Prove2me | Theorems.Thm_GravitationalConstant_einstein_constant_determines_newton_constant
-- name    : GravitationalConstant.einstein_constant_determines_newton_constant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T13:53:07.827667+00:00
-- url     : https://prove2.me/theorems/ca6a9a90-46eb-4d93-bad5-e025d2f846ce
-- title:
--   Einstein gravitational constant: $G = \kappa c^4/(8\pi)$
-- statement:
--   The Einstein gravitational constant appearing in the Einstein field equations is $\kappa = 8\pi G/c^4$, where $c$ is the speed of light. It carries exactly the same information as the Newtonian constant: for $c \neq 0$,
--
--   $$ G = \frac{\kappa c^{4}}{8\pi}. $$
-- source:
--   Wikipedia, "Gravitational constant" (uploaded PDF `Gravitational_constant.pdf`), https://en.wikipedia.org/wiki/Gravitational_constant — sections "Definition", "Value and uncertainty", "Orbital mechanics", "History of measurement".

import Definitions.Def_GravitationalConstantBasic

namespace GravitationalConstant

theorem einstein_constant_determines_newton_constant
    (G c : ℝ) (hc : c ≠ 0) :
    G = einsteinConstant G c * c ^ 4 / (8 * Real.pi) := by sorry

end GravitationalConstant
