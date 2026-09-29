-- Prove2me | Theorems.Thm_GKP1998_partial_wave_flux_factor
-- name    : GKP1998.partial_wave_flux_factor
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-26T00:47:03.198934+00:00
-- url     : https://prove2.me/theorems/685b0e15-4f4d-4300-ac21-e3b379e62d70
-- title:
--   Eqs. (36)–(37) (sign corrected): flux factor of the $l$-th partial wave
-- statement:
--   For every $l\in\mathbb N$ and $R>0$ there is a function $A$, real-analytic at $0$, such that as $k\to0^+$
--   $$\mathcal F_{l+2}(k)=A(k^2)-\frac{(-1)^l}{2^{2l+2}\,((l+1)!)^2}\,k^{4+2l}R^{2l}\log(kR)+o\big(k^{4+2l}\big),$$
--   where $\mathcal F_\nu(k)=\big[z^{-3}\partial_z\log\tilde f_k(z)\big]_{z=R}$ and $\tilde f_k(z)=z^2K_\nu(kz)/(R^2K_\nu(kR))$.
--
--   **Deviation from the source.** Eq. (37) prints the coefficient $+\frac{(-1)^l}{2^{2l+2}((l+1)!)^2}$. Numerical exploration by the drafter (not machine-checked; high-precision fits for $l=0,1$ gave $-0.25$ and $+0.015625$) supports the opposite sign, consistent with the standard expansion $K_n(x)\ni(-1)^{n+1}\log(x/2)I_n(x)$ (DLMF 10.31.1). Eq. (27), the case $l=0$, prints $-\frac14k^4\log(k^2R^2)$, which also disagrees with Eq. (37); the value here gives $-\frac14k^4\log(kR)$ for $l=0$. The statement is drafted with the corrected coefficient; please confirm this choice.
-- source:
--   S.S. Gubser, I.R. Klebanov, A.M. Polyakov, Gauge theory correlators from non-critical string theory, Phys. Lett. B 428 (1998) 105-114, arXiv:hep-th/9802109, p. 111, Eqs. (36)-(37) (sign of log coefficient corrected; cf. Eq. (27), p. 110)

import Definitions.Def_GKP1998_Defs

open Filter Topology Asymptotics

namespace GKP1998
/-- Eqs. (36)–(37), with the sign of the logarithmic coefficient corrected (see the item's
description): for the `l`-th partial wave the flux factor is an analytic function of `k²`
plus the leading non-analytic term
`−(−1)^l / (2^{2l+2} ((l+1)!)²) · k^{4+2l} R^{2l} log(kR)`, up to `o(k^{4+2l})` as `k → 0⁺`. -/
theorem partial_wave_flux_factor (l : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ A : ℝ → ℝ, AnalyticAt ℝ A 0 ∧
      (fun k : ℝ => fluxFactor ((l : ℝ) + 2) k R - A (k ^ 2)
          - (-(-1 : ℝ) ^ l / (2 ^ (2 * l + 2) * ((l + 1).factorial : ℝ) ^ 2))
              * k ^ (2 * l + 4) * R ^ (2 * l) * Real.log (k * R))
        =o[𝓝[>] (0 : ℝ)] (fun k : ℝ => k ^ (2 * l + 4)) := by sorry
end GKP1998
