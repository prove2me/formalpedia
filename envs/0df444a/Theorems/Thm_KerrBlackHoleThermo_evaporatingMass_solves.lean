-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_evaporatingMass_solves
-- name    : KerrBlackHoleThermo.evaporatingMass_solves
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:48:55.386534+00:00
-- url     : https://prove2.me/theorems/a588354e-9e1d-494b-81f4-7ef9629883fb
-- title:
--   Black-hole evaporation: $M(t) = (M_0^3 - t/256\pi)^{1/3}$ solves $\dot M = -(768\pi)^{-1}M^{-2}$
-- statement:
--   Let $M_0>0$ and let
--   $$M(t) = \left(M_0^3 - \frac{t}{256\pi}\right)^{1/3}.$$
--   Then $M(0)=M_0$, and for every time $t<256\pi M_0^3$ the function $M$ is differentiable at $t$ with
--   $$\frac{dM}{dt}(t) = -\frac{(768\pi)^{-1}}{M(t)^2}.$$
--
--   This is the evaporation law of a Schwarzschild black hole under the Hawking energy flux $F=(768\pi)^{-1}M^{-2}$ (eqs. (4.135)–(4.137) of the dissertation): (4.137) solves the mass-loss equation (4.136), and the black hole evaporates completely at $t=256\pi M_0^3$.
--
--   **Formalization Note** The statement is restricted to $t<256\pi M_0^3$, where the base $M_0^3-t/256\pi$ is positive and the real cube root is unambiguous.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 4.4.1, eqs. (4.135)–(4.137), p. 116

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eqs. (4.136)–(4.137): `M(t) = (M₀³ − t / 256π)^{1/3}` satisfies `M(0) = M₀` and
`dM/dt = −(768 π)⁻¹ / M²` for every `t < 256 π M₀³`. -/
theorem evaporatingMass_solves (M₀ : ℝ) (hM₀ : 0 < M₀) :
    evaporatingMass M₀ 0 = M₀ ∧
    ∀ t : ℝ, t < 256 * π * M₀ ^ 3 →
      HasDerivAt (evaporatingMass M₀)
        (-(768 * π)⁻¹ / evaporatingMass M₀ t ^ 2) t := by
  sorry

end KerrBlackHoleThermo
