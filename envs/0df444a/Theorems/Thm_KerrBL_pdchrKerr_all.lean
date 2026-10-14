-- Prove2me | Theorems.Thm_KerrBL_pdchrKerr_all
-- name    : KerrBL.pdchrKerr_all
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:36:06.880645+00:00
-- url     : https://prove2.me/theorems/0f006266-cb40-4e95-8673-8679371ebd3a
-- title:
--   $\partial_l\Gamma^i_{jk}$ of the generic Kerr Christoffel symbols equals the closed form
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all $l,i,j,k\in\{0,1,2,3\}$,
--
--   $$\partial_l\,\Gamma^i_{jk}(x)=\texttt{dGammaKerr}\ M\ a\ l\ i\ j\ k\ \big(r,\sin\theta,\cos\theta,\Sigma,\Delta\big)(x),$$
--
--   where $\partial_l$ is the slice derivative `KerrBL.pd` applied to the generic Christoffel symbol `christoffel (gKerr M a) (giKerr M a) i j k`.
--
--   This is the `deriv`-valued form of `hdchrKerr_all`, consumed by the Ricci bridge `ricci_bridge_Kerr`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N11 (pdchrKerr_all)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.pdchrKerr_all (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j k : Fin 4, pd l (christoffel (gKerr M a) (giKerr M a) i j k) x = dGammaKerr M a l i j k (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) := by sorry
