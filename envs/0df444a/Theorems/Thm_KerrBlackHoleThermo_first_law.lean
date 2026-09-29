-- Prove2me | Theorems.Thm_KerrBlackHoleThermo_first_law
-- name    : KerrBlackHoleThermo.first_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T19:46:25.05301+00:00
-- url     : https://prove2.me/theorems/e484a472-bcbd-4a94-bed6-721d6aac1597
-- title:
--   First law of black-hole mechanics for Kerr: $\delta M = \frac{\kappa}{8\pi}\delta A + \Omega_H\,\delta J$
-- statement:
--   Parametrize Kerr black holes by their mass $M$ and angular momentum $J$ (rotation parameter $a=J/M$), and let $A(M,J)$ be the area of the event horizon (computed from the Kerr metric, see the definition file), $\kappa$ the surface gravity (eq. (3.3)) and $\Omega_H$ the angular velocity of the horizon (eq. (2.42)). Let $M>0$ and $J^2<M^4$ (a non-extremal black hole). Then $A$ is differentiable at $(M,J)$, and for every variation $(\delta M,\delta J)$
--   $$\delta M = \frac{\kappa}{8\pi}\,\delta A + \Omega_H\,\delta J, \qquad \delta A = dA_{(M,J)}(\delta M,\delta J).$$
--
--   This is the first law of black-hole mechanics of Bardeen, Carter and Hawking for stationary (Kerr) black holes, eq. (3.79) of the dissertation. Combined with the Hawking temperature $T_{BH}=\kappa/2\pi$ (eq. (4.113)) it reads $\delta M = T_{BH}\,\delta S_{BH} + \Omega_H\,\delta J$ with $S_{BH}=A/4$ (eq. (4.114)).
--
--   **Formalization Note** The first-order variations between neighbouring Kerr configurations are formalized as the Fréchet derivative of the explicit Kerr family in the coordinates $(M,J)$. The hypothesis $J^2<M^4$ excludes the extremal limit, where $A$ is not differentiable.
-- source:
--   F. H. de C. Menezes, Termodinâmica de Buracos Negros, M.Sc. dissertation, Programa de Pós-Graduação em Física, ICEx, Universidade Federal de Minas Gerais, Belo Horizonte, 2021 (advisor: N. de O. Yokomizo), Section 3.2.4, eq. (3.79), p. 74 (cf. eqs. (3.45), (3.78))

import Mathlib
import Definitions.Def_KerrBlackHoleThermo_Defs

open Real

namespace KerrBlackHoleThermo

/-- Goal, eq. (3.79) — first law of black-hole mechanics for the Kerr family:
along the non-extremal Kerr family parametrised by `(M, J)` (so `a = J / M`),
`δM = (κ / 8π) δA + Ω_H δJ`. -/
theorem first_law (M J : ℝ) (hM : 0 < M) (hJ : J ^ 2 < M ^ 4) :
    ∃ dA : ℝ × ℝ →L[ℝ] ℝ,
      HasFDerivAt (fun p : ℝ × ℝ => horizonArea p.1 (p.2 / p.1)) dA (M, J) ∧
      ContinuousLinearMap.fst ℝ ℝ ℝ
        = (surfaceGravity M (J / M) / (8 * π)) • dA
          + horizonAngularVelocity M (J / M) • ContinuousLinearMap.snd ℝ ℝ ℝ := by
  sorry

end KerrBlackHoleThermo
