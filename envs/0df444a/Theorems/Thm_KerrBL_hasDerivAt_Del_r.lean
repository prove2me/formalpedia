-- Prove2me | Theorems.Thm_KerrBL_hasDerivAt_Del_r
-- name    : KerrBL.hasDerivAt_Del_r
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:28:27.03833+00:00
-- url     : https://prove2.me/theorems/ba629de8-538f-4707-a081-b37755a81cc1
-- title:
--   $\partial_r\Delta = 2r-2M$
-- statement:
--   For all real $M,a,r$ the function $u\mapsto\Delta(M,a,u)=a^2+u^2-2Mu$ has derivative $-2M+2r$ at $u=r$, in the sense of `HasDerivAt`.
--
--   Atom lemma of Layer II: the radial derivative of $\Delta$, consumed by `hdgKerr_all` and `hdchrKerr_all` through the chain rule.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N4 (hasDerivAt_Del_r)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.hasDerivAt_Del_r (M a r : ℝ) : HasDerivAt (fun u => Del M a u) (((-2))*M + 2*r) r := by sorry
