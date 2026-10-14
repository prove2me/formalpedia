-- Prove2me | Theorems.Thm_KerrBL_hasDerivAt_Sig_th
-- name    : KerrBL.hasDerivAt_Sig_th
-- status  : Proved
-- author  : @He Wang
-- created : 2026-09-09T09:28:13.024986+00:00
-- url     : https://prove2.me/theorems/944166a6-0c9b-4fbd-b82b-5b9ed9da0d6e
-- title:
--   $\frac{d}{d\theta}\,\Sigma(r,\cos\theta) = -2a^2\sin\theta\cos\theta$
-- statement:
--   For all real $a,r,\theta$ the function $\theta\mapsto\Sigma(a,r,\cos\theta)=r^2+a^2\cos^2\theta$ has derivative
--
--   $$-2\,\sin\theta\,\cos\theta\,a^2$$
--
--   at $\theta$, in the sense of `HasDerivAt`.
--
--   Atom lemma of Layer II: the $\theta$-derivative of $\Sigma$ along the angular coordinate, consumed by `hdgKerr_all` and `hdchrKerr_all` through the chain rule.
-- source:
--   R. P. Kerr, Gravitational field of a spinning mass as an example of algebraically special metrics, Phys. Rev. Lett. 11 (1963) 237-238, https://doi.org/10.1103/PhysRevLett.11.237; R. H. Boyer and R. W. Lindquist, Maximal analytic extension of the Kerr metric, J. Math. Phys. 8 (1967) 265-281, https://doi.org/10.1063/1.1705193, Sec. 2 (Boyer-Lindquist form of the Kerr line element); metric components transcribed token-for-token from the project certificate EinsteinSolver/certificate/kerr/metric.json (sha256 d729883d95fd7d3cf84d9c971c6725f847155562cc4e88660535b8d0bd0be336); design record LEAN/kerr-formalization/mission/DESIGN.md, node N3 (hasDerivAt_Sig_th)

import Definitions.Def_KerrBL_Kerr_Metric
open KerrBL Filter Topology

theorem KerrBL.hasDerivAt_Sig_th (a r θ : ℝ) : HasDerivAt (fun θ => Sig a r (Real.cos θ)) (((-2))*Real.sin θ*Real.cos θ*a^(2:ℕ)) θ := by sorry
