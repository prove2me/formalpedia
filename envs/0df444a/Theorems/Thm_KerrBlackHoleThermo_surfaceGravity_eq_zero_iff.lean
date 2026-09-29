-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_surfaceGravity_eq_zero_iff
-- name    : KerrBlackHoleThermo.surfaceGravity_eq_zero_iff
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T19:48:02.103384+00:00
-- url     : https://prove2.me/theorems/0e895136-a451-4b51-a3c9-39b9f2ac9d70
-- title:
--   Kerr surface gravity vanishes iff $|J| = M^2$
-- statement:
--   Let $M>0$ and $a$ be real numbers with $a^2\le M^2$ (a Kerr black hole, possibly extremal), with angular momentum $J=Ma$ and surface gravity $\kappa$ given by eq. (3.3). Then
--   $$\kappa = 0 \iff |J| = M^2.$$
--
--   This is the observation following eq. (3.81) of the dissertation: black holes satisfy $M^2\ge J$, and turning a black hole into a naked singularity would require passing through the extremal configuration $M^2=J$, which is exactly where $\kappa=0$. It is the formal content behind the dissertation's formulation of the third law (no finite process reaches $\kappa=0$).
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.4, eq. (3.81) and the following paragraph, p. 78

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, discussion after eq. (3.81): for a Kerr black hole (`a² ≤ M²`), the surface
gravity vanishes exactly in the extremal case `|J| = M²`. -/
theorem surfaceGravity_eq_zero_iff (M a : ℝ) (hM : 0 < M) (ha : a ^ 2 ≤ M ^ 2) :
    surfaceGravity M a = 0 ↔ |angMom M a| = M ^ 2 := by
  sorry

end KerrBlackHoleThermo
