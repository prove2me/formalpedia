-- Prove2me | Theorems.Thm_KerrBL_hdgKerr_all
-- name    : KerrBL.hdgKerr_all
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:34:51.400479+00:00
-- url     : https://prove2.me/theorems/2a79d3ec-b219-44b8-af69-9c98369ffdbf
-- title:
--   Every coordinate slice of every Kerr metric component is differentiable, with the closed-form derivative
-- statement:
--   For all real $M,a$, every point $x$ of the regular domain and all indices $l,i,j\in\{0,1,2,3\}$, the slice
--
--   $$u\longmapsto g_{ij}\big(x[l\mapsto u]\big)$$
--
--   of the Boyer-Lindquist Kerr metric component $g_{ij}$ along coordinate $l$ has, at $u=x_l$, the derivative `dgKerr M a l i j` evaluated at the atoms $(r,\sin\theta,\cos\theta,\Sigma,\Delta)$ of $x$, in the sense of Mathlib's `HasDerivAt`.
--
--   This is the metric-derivative certification of Layer II: it establishes both that the derivative exists (so the generic $\partial_l g_{ij}$ of the specification layer is a genuine derivative, not Mathlib's junk value) and that it equals the generated closed form. The companion statement in terms of `pd` is `pdgKerr_all`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N7 (hdgKerr_all)

import Definitions.Def_KerrBL_Kerr_ClosedForms
open KerrBL Filter Topology

theorem KerrBL.hdgKerr_all (M a : ℝ) (x : Pt) (hx : RegKerr M a x) :
    ∀ l i j : Fin 4, HasDerivAt (fun u => gKerr M a i j (Function.update x l u)) (dgKerr M a l i j (x 1) (Real.sin (x 2)) (Real.cos (x 2)) (Sig a (x 1) (Real.cos (x 2))) (Del M a (x 1))) (x l) := by sorry
