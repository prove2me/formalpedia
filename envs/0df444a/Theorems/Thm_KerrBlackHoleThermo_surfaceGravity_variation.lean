-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_surfaceGravity_variation
-- name    : KerrBlackHoleThermo.surfaceGravity_variation
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-25T19:46:01.774991+00:00
-- url     : https://prove2.me/theorems/88015e27-7727-4ed0-9577-44db583509f8
-- title:
--   Variation of $\kappa$ along the Kerr family: $\delta M = -\frac{A}{4\pi}\delta\kappa - 2J\,\delta\Omega_H$
-- statement:
--   Parametrize Kerr black holes by their mass $M$ and angular momentum $J$ (so that the rotation parameter is $a=J/M$), and regard the surface gravity $\kappa$, the horizon angular velocity $\Omega_H$ and the horizon area $A$ as functions of $(M,J)$. Let $M>0$ and $J^2<M^4$ (a non-extremal black hole, $|J|<M^2$). Then $\kappa$ and $\Omega_H$ are differentiable at $(M,J)$, and their differentials satisfy
--   $$\delta M = -\frac{A}{4\pi}\,\delta\kappa - 2J\,\delta\Omega_H,$$
--   i.e. as linear forms on variations $(\delta M,\delta J)$,
--   $$\delta M = -\frac{A}{4\pi}\,d\kappa_{(M,J)}(\delta M,\delta J) - 2J\,d\Omega_{H,(M,J)}(\delta M,\delta J).$$
--
--   This is the relation for the variation of $\kappa$ between two neighbouring Kerr configurations, eq. (3.78) of the dissertation. Added to the variation of the Smarr formula (3.45) it yields the first law (3.79).
--
--   **Formalization Note** The dissertation prints the last coefficient as $-2\pi J\,\delta\Omega_H$. Its own intermediate equations (3.70) and (3.77) give $-8\pi\,\delta M = 2A\,\delta\kappa + 16\pi J\,\delta\Omega_H$, i.e. the coefficient $-2J$, and only $-2J$ cancels the term $2J\,\delta\Omega_H$ of (3.45) to produce (3.79); the statement uses $-2J$. The variation is formalized as the Fréchet derivative along the explicit Kerr family; the non-extremality hypothesis $J^2<M^4$ is needed because $\kappa$ is not differentiable at the extremal limit.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.2.4, eqs. (3.70), (3.77), (3.78), pp. 72–74

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Milestone, eq. (3.78) (with the coefficient of `δΩ_H` read as `−2J`; see the proposal):
along the non-extremal Kerr family parametrised by `(M, J)` (so `a = J / M`),
`δM = −(A / 4π) δκ − 2 J δΩ_H`. -/
theorem surfaceGravity_variation (M J : ℝ) (hM : 0 < M) (hJ : J ^ 2 < M ^ 4) :
    ∃ dκ dΩ : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => surfaceGravity p.1 (p.2 / p.1)) dκ (M, J) ∧
      HasFDerivAt (fun p : ℝ × ℝ => horizonAngularVelocity p.1 (p.2 / p.1)) dΩ (M, J) ∧
      ContinuousLinearMap.fst ℝ ℝ ℝ
        = (-(horizonArea M (J / M) / (4 * π))) • dκ - (2 * J) • dΩ := by
  sorry

end KerrBlackHoleThermo
