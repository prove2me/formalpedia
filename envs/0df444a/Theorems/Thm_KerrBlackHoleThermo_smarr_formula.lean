-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_smarr_formula
-- name    : KerrBlackHoleThermo.smarr_formula
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:45:40.496556+00:00
-- url     : https://prove2.me/theorems/9724d6bc-6e2b-4e41-8374-5a4ef06a88cc
-- title:
--   Smarr formula for Kerr: $M = \kappa A/(4\pi) + 2\Omega_H J$
-- statement:
--   Let $M>0$ and $a$ be real numbers with $a^2\le M^2$, and consider the Kerr black hole of mass $M$ and angular momentum $J=Ma$. Let $\kappa$ be its surface gravity (eq. (3.3)), $\Omega_H$ the angular velocity of its horizon (eq. (2.42)) and $A$ the area of its event horizon (computed from the metric, see the definition file). Then
--   $$M = \frac{\kappa A}{4\pi} + 2\,\Omega_H J.$$
--
--   This is the Smarr relation, eq. (3.43) of the dissertation, obtained there from the Komar integrals for the mass and the angular momentum. Its first-order variation, eq. (3.45), is one of the two ingredients of the first law.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.2.3, eq. (3.43), p. 66

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eq. (3.43): Smarr formula `M = κ A / (4 π) + 2 Ω_H J`. -/
theorem smarr_formula (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    M = surfaceGravity M a * horizonArea M a / (4 * π)
      + 2 * horizonAngularVelocity M a * angMom M a := by
  sorry

end KerrBlackHoleThermo
