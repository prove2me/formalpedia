-- Prove2me | Theorems.Thm_KerrBL_chrKerr_all
-- name    : KerrBL.chrKerr_all
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:35:22.747007+00:00
-- url     : https://prove2.me/theorems/9427383d-3a48-47f8-834b-97c478395685
-- title:
--   Generic Christoffel symbols of the Kerr metric equal the closed-form Christoffel symbols
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all indices $i,j,k\in\{0,1,2,3\}$,
--
--   $$\Gamma^i_{jk}(x)\;=\;\texttt{GammaKerrpt}\ M\ a\ i\ j\ k\ x,$$
--
--   where the left-hand side is the generic coordinate Christoffel symbol `christoffel (gKerr M a) (giKerr M a) i j k x` of the specification layer, computed from the metric, the candidate inverse and the slice derivatives, and the right-hand side is the generated closed form evaluated at the atoms of $x$.
--
--   This is the Christoffel bridge of Layer II. Downstream, the closed forms are differentiated (`hdchrKerr_all`) and substituted into the Ricci formula (`ricci_bridge_Kerr`).
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N9 (chrKerr_all)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.chrKerr_all (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ i j k : Fin 4, christoffel (gKerr M a) (giKerr M a) i j k x = GammaKerrpt M a i j k x := by sorry
