-- Prove2me | Theorems.Thm_KerrBL_reg_eventually_Kerr
-- name    : KerrBL.reg_eventually_Kerr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:30:56.60216+00:00
-- url     : https://prove2.me/theorems/d29d69ce-9f08-4bd0-af54-3f6f43999518
-- title:
--   The regular domain of the Kerr metric is open
-- statement:
--   For all real $M,a$ and every point $x\in\mathbb R^4$: if $x$ lies in the regular domain
--
--   $$\Sigma(x)\neq0,\qquad \Delta(x)\neq0,\qquad \sin x_2\neq0,$$
--
--   then every point of some neighbourhood of $x$ (product topology on $\mathbb R^4$) lies in the regular domain as well.
--
--   This openness statement is what allows Layer II to pass from *the generic Christoffel symbol equals the closed form at every regular point* to differentiability of the generic Christoffel symbol at $x$: the two functions agree on a whole neighbourhood, so their slice derivatives coincide.
--
--   **Formalization Note** Stated as `∀ᶠ y in 𝓝 x, RegKerr M a y`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N6 (reg_eventually_Kerr)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.reg_eventually_Kerr (M a : ℝ) (x : Pt) (hx : RegKerr M a x) : ∀ᶠ y in 𝓝 x, RegKerr M a y := by sorry
