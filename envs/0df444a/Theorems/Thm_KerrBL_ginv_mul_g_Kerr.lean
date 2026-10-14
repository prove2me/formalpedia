-- Prove2me | Theorems.Thm_KerrBL_ginv_mul_g_Kerr
-- name    : KerrBL.ginv_mul_g_Kerr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:27:31.283648+00:00
-- url     : https://prove2.me/theorems/b4ddd0d5-1d74-4a4b-b5a6-20e5e1e6a08e
-- title:
--   The closed-form matrix is a left inverse of the Boyer-Lindquist Kerr metric
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain ($\Sigma\neq0$, $\Delta\neq0$, $\sin\theta\neq0$) and all indices $i,j\in\{0,1,2,3\}$,
--
--   $$\sum_{k=0}^{3}\hat g^{ik}(x)\,g_{kj}(x)=\delta_{ij},$$
--
--   where $g$ is the Boyer-Lindquist Kerr metric and $\hat g$ the closed-form candidate inverse of `KerrBL_Kerr_Metric`.
--
--   This is Layer I of the mission. The generic Christoffel symbols take the inverse as data, so the Ricci-flatness statement would be vacuous for a wrong candidate (for $\hat g=0$ every $\Gamma$ vanishes). This theorem removes that loophole and is bundled into the headline `vacuum_Kerr`.
--
--   **Formalization Note** Stated componentwise with `if i = j then 1 else 0`. Only the left inverse $\hat g g=I$ is asserted; the two-sided statement follows mathematically but is not part of the text.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N1 (ginv_mul_g_Kerr)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.ginv_mul_g_Kerr (M a : ℝ) (x : Pt) (hx : RegKerr M a x) (i j : Fin 4) :
    (∑ k : Fin 4, giKerr M a i k x * gKerr M a k j x) = (if i = j then 1 else 0) := by sorry
