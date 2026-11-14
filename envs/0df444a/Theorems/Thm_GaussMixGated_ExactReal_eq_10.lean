-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_eq_10
-- name    : GaussMixGated.ExactReal.eq_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-11T15:26:00.292425+00:00
-- url     : https://prove2.me/theorems/7314d889-61b1-4bda-a447-7c373254647f
-- title:
--   §2.1, display (10) — $R_0/\sigma_0\le\sqrt{L_*}$
-- statement:
--   Let $d,k\ge1$, $0<\varepsilon,\delta<1/4$ and $C_{\mathrm{cov}}\ge1$, and form the schedule (7)–(9): $A_*=1+2C_{\mathrm{cov}}$, $H=\log(1/\delta)$, $J=\lceil\log_432(d+H+2)\rceil$, $\beta=\varepsilon^2/(1000(J+1)A_*^{J+1})$, $L_*=\log(2k/\beta)$, $\sigma_0=2^J$, $N_0=\lceil(k/\beta)\log(16k/\delta)\rceil$ and $R_0=\sqrt d+\sqrt{2\log(16N_0/\delta)}$. Then
--
--   $$\frac{R_0}{\sigma_0}\le\sqrt{L_*}.$$
--
--   The initial cover radius therefore costs only a $\sqrt{L_*}$ factor in the dictionary's $\exp(O((r/\sigma)^2))$ term, even when $\delta$ is very small.
--
--   Differences from the source:
--   - generalization: C_cov is the universal constant of Theorem 2.3 (C_cov ≥ 1) → any real C_cov ≥ 1; reason: the display uses only C_cov ≥ 1; it specializes to the constant of Theorem 2.3
--   - encoding: ceilings and log₄ → Nat.ceil and log x / log 4; reason: Lean convention; the arguments are positive
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 7 (printed p. 5), §2.1, display (10)

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Schedule

namespace GaussMixGated.ExactReal

/-- §2.1, display (10) (Zheng–Xie–He, STOC 2027 #36, PDF p. 7): with the schedule (7)–(9),
`R₀ / σ₀ ≤ √L*`. -/
theorem eq_10 (d k : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (ε δ : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 4)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (Ccov : ℝ) (hC : 1 ≤ Ccov) :
    R0sched d k ε δ Ccov / sigmaSched d δ 0 ≤ Real.sqrt (Lstar d k ε δ Ccov) := by sorry

end GaussMixGated.ExactReal
