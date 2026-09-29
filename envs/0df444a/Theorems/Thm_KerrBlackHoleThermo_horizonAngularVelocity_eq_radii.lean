-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_horizonAngularVelocity_eq_radii
-- name    : KerrBlackHoleThermo.horizonAngularVelocity_eq_radii
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:41:50.236989+00:00
-- url     : https://prove2.me/theorems/980f565f-11ba-458c-879a-5719262cd7f7
-- title:
--   Kerr horizon angular velocity: $\Omega_H = a/(r_+^2+a^2)$
-- statement:
--   Let $M>0$ and $a$ be real numbers with $a^2\le M^2$ (a Kerr black hole of mass $M$ and rotation parameter $a$, possibly extremal), and let $r_+ = M+\sqrt{M^2-a^2}$ be the radius of the event horizon. Then the angular velocity of the horizon,
--   $$\Omega_H = \frac{a}{2M\left(M+\sqrt{M^2-a^2}\right)},$$
--   can be rewritten in terms of $r_+$ as
--   $$\Omega_H = \frac{a}{r_+^2+a^2}.$$
--
--   This is the second equality of eq. (2.42) of the dissertation; it expresses $\Omega_H$ through the horizon radius, the form in which it enters the horizon Killing field $\chi^a=\xi^a+\Omega_H\psi^a$.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 2.4, eq. (2.42), p. 52

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eq. (2.42), second equality: `Ω_H = a / (r₊² + a²)`. -/
theorem horizonAngularVelocity_eq_radii (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    horizonAngularVelocity M a = a / (rPlus M a ^ 2 + a ^ 2) := by
  sorry

end KerrBlackHoleThermo
