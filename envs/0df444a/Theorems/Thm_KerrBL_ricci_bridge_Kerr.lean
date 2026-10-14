-- Prove2me | Theorems.Thm_KerrBL_ricci_bridge_Kerr
-- name    : KerrBL.ricci_bridge_Kerr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:36:24.798231+00:00
-- url     : https://prove2.me/theorems/a3855832-b52d-4060-9c58-27cd030b1d94
-- title:
--   The generic Ricci tensor of the Kerr metric equals the explicit closed-form expression
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all indices $b,d\in\{0,1,2,3\}$,
--
--   $$R_{bd}(x)\;=\;\texttt{RicciKerr}\ M\ a\ b\ d\ \big(r,\sin\theta,\cos\theta,\Sigma,\Delta\big)(x),$$
--
--   where $R_{bd}=$ `ricciOf (gKerr M a) (giKerr M a) b d x` is the generic derivative-based coordinate Ricci tensor of the specification layer, and `RicciKerr` is the explicit expression of `KerrBL_Kerr_ClosedForms`.
--
--   This is the bridge from the specification to the explicit expressions whose vanishing Layer III proves. The explicit Ricci expression is never assumed: this theorem derives it from the generic definitions together with the Christoffel bridge and the Christoffel-derivative certification.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N12 (ricci_bridge_Kerr)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.ricci_bridge_Kerr (M a : ℝ) (x : Pt) (hx : RegKerr M a x) (b d : Fin 4) :
    ricciOf (gKerr M a) (giKerr M a) b d x = RicciKerr M a b d (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1)) := by sorry
