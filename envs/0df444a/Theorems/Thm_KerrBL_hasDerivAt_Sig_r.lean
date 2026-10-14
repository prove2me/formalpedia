-- Prove2me | Theorems.Thm_KerrBL_hasDerivAt_Sig_r
-- name    : KerrBL.hasDerivAt_Sig_r
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:27:56.239856+00:00
-- url     : https://prove2.me/theorems/861a0954-b298-41a8-a610-809c9f48250b
-- title:
--   $\partial_r\Sigma = 2r$
-- statement:
--   For all real $a,r,c$ the function $u\mapsto\Sigma(a,u,c)=u^2+a^2c^2$ has derivative $2r$ at $u=r$, in the sense of Mathlib's `HasDerivAt`.
--
--   Atom lemma of Layer II: the derivative of the abbreviation $\Sigma$ with respect to $r$, consumed by the metric-derivative theorem `hdgKerr_all` through the chain rule.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N2 (hasDerivAt_Sig_r)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.hasDerivAt_Sig_r (a r c : ℝ) : HasDerivAt (fun u => Sig a u c) (2*r) r := by sorry
