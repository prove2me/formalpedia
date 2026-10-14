-- Prove2me | Theorems.Thm_KerrBL_pdgKerr_all
-- name    : KerrBL.pdgKerr_all
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:35:09.939748+00:00
-- url     : https://prove2.me/theorems/41eb9df3-67cd-4953-a12c-f9e6de744fa3
-- title:
--   $\partial_l g_{ij}$ of the Kerr metric equals the closed form
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all $l,i,j\in\{0,1,2,3\}$,
--
--   $$\partial_l\, g_{ij}(x) = \texttt{dgKerr}\ M\ a\ l\ i\ j\ \big(r,\sin\theta,\cos\theta,\Sigma,\Delta\big)(x),$$
--
--   where $\partial_l$ is the slice derivative `KerrBL.pd` of the generic layer and the right-hand side is the generated closed form.
--
--   This is the form of the metric-derivative certification that the Christoffel bridge `chrKerr_all` consumes. It is the `deriv`-valued shadow of `hdgKerr_all`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N8 (pdgKerr_all)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.pdgKerr_all (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j : Fin 4, pd l (gKerr M a i j) x = dgKerr M a l i j (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) := by sorry
