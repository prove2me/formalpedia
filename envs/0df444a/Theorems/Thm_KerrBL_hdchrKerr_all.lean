-- Prove2me | Theorems.Thm_KerrBL_hdchrKerr_all
-- name    : KerrBL.hdchrKerr_all
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:35:43.833875+00:00
-- url     : https://prove2.me/theorems/6727f6e8-0835-4772-8154-4937ec16368d
-- title:
--   Every coordinate slice of every generic Christoffel symbol of Kerr is differentiable, with the closed-form derivative
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all indices $l,i,j,k\in\{0,1,2,3\}$, the slice
--
--   $$u\longmapsto \Gamma^i_{jk}\big(x[l\mapsto u]\big)$$
--
--   of the **generic** Christoffel symbol `christoffel (gKerr M a) (giKerr M a) i j k` along coordinate $l$ has, at $u=x_l$, the derivative `dGammaKerr M a l i j k` evaluated at the atoms of $x$, in the sense of `HasDerivAt`.
--
--   This is the second differentiability certification of Layer II. It concerns the generic object, not the closed form, so that the second derivatives entering the Ricci formula are genuine derivatives of the Christoffel symbols defined in the specification layer. The `pd`-valued companion is `pdchrKerr_all`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N10 (hdchrKerr_all)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.hdchrKerr_all (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j k : Fin 4, HasDerivAt (fun u => christoffel (gKerr M a) (giKerr M a) i j k (Function.update x l u)) (dGammaKerr M a l i j k (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x l) := by sorry
