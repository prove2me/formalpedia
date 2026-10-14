-- Prove2me | Theorems.Thm_KerrBL_ricci_flat_Kerr
-- name    : KerrBL.ricci_flat_Kerr
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:36:39.226821+00:00
-- url     : https://prove2.me/theorems/5205f4b2-8cf7-4611-83b3-f950df3e03a9
-- title:
--   All sixteen coordinate Ricci components of the Kerr metric vanish on the regular domain
-- statement:
--   For all real $M,a$, every point $x=(t,r,\theta,\varphi)\in\mathbb R^4$ with
--
--   $$\Sigma=r^2+a^2\cos^2\theta\neq0,\qquad \Delta=r^2-2Mr+a^2\neq0,\qquad \sin\theta\neq0,$$
--
--   and all indices $b,d\in\{0,1,2,3\}$,
--
--   $$R_{bd}(x)=0,$$
--
--   where $R_{bd}=$ `ricciOf (gKerr M a) (giKerr M a) b d x` is the coordinate Ricci tensor of the specification layer: the standard formula $R_{bd}=\sum_i(\partial_i\Gamma^i_{bd}-\partial_d\Gamma^i_{bi}+\sum_j(\Gamma^i_{ij}\Gamma^j_{bd}-\Gamma^i_{dj}\Gamma^j_{bi}))$ with $\Gamma^a_{bc}=\tfrac12\sum_k\hat g^{ak}(\partial_cg_{kb}+\partial_bg_{kc}-\partial_kg_{bc})$, evaluated on the Boyer-Lindquist Kerr metric $g$ and its closed-form inverse $\hat g$ with Mathlib's slice derivatives.
--
--   This is Ricci-flatness of the Boyer-Lindquist Kerr family on the regular coordinate domain of the formalization, for arbitrary real parameters $M,a$. It is not a global Lorentzian-manifold statement and it is not restricted to the black-hole regime. All sixteen components are proved separately; no symmetry of $R_{bd}$ is used or asserted.
--
--   **Formalization Note** Only the generic definitions appear in the statement; no closed form is mentioned. Read together with `ginv_mul_g_Kerr` (the inverse is genuine) and the differentiability theorems `hdgKerr_all`, `hdchrKerr_all` (no junk derivative values), as packaged in `vacuum_Kerr`.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N22 (ricci_flat_Kerr)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.ricci_flat_Kerr (M a : ℝ) (x : Pt) (hx : RegKerr M a x) (b d : Fin 4) :
    ricciOf (gKerr M a) (giKerr M a) b d x = 0 := by sorry
