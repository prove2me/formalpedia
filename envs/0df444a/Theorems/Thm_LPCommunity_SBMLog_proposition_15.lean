-- Prove2me | Theorems.Thm_LPCommunity_SBMLog_proposition_15
-- name    : LPCommunity.SBMLog.proposition_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:23.809591+00:00
-- url     : https://prove2.me/theorems/e83f586d-28e4-4612-a38d-9a195e05ca82
-- title:
--   Proposition 15, p. 29 — the average distance of G_{n,α log n/n} is (1 ± ϵ) log n/log(pn) w.h.p.
-- statement:
--   Let $\alpha>1$, $p=\alpha\frac{\log n}{n}$, and $G\sim\mathcal G_{n,p}$. Write $\rho_{\mathrm{avg}}(G)=\frac{2}{n^2}\sum_{i<j}\rho_G(i,j)$ for the average distance. Then for every $\epsilon>0$,
--   $$
--   \lim_{n\to\infty}\mathbb P\left[\rho_{\mathrm{avg}}(G)\in\left((1-\epsilon)\frac{\log n}{\log pn},\ (1+\epsilon)\frac{\log n}{\log pn}\right)\right]=1.
--   $$
--
--   This is Theorem 1 of Chung and Lu (2002) as restated in the paper. Through the coupling of Proposition 11 it gives the lower bound on the average distance in the logarithmic-degree SBM (Proposition 19).
--
--   **Formalization Note** The denominator is $\log(pn)$ as printed, here $\log(\alpha\log n)$, not $\log\log n$. The interval is open, as printed. $\rho_{\mathrm{avg}}$ is compared in $[0,\infty]$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 29, Proposition 15 (Theorem 1 of [13])

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

namespace LPCommunity.SBMLog

/-- Proposition 15 (arXiv:2006.03213v2, p. 29; Theorem 1 of Chung–Lu [13]). For
`p = α log n / n` with `α > 1` and `G ∼ G_{n,p}`, for every `ε > 0` the average distance
`ρ_avg(G)` lies in the open interval `((1 − ε) log n / log(pn), (1 + ε) log n / log(pn))` with
probability tending to `1`. -/
theorem proposition_15 (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (logRegime α n) (fun G =>
        ENNReal.ofReal ((1 - ε) * (Real.log n / Real.log (logRegime α n * n))) < LPCommunity.LPFail.rhoAvg G ∧
        LPCommunity.LPFail.rhoAvg G < ENNReal.ofReal ((1 + ε) * (Real.log n / Real.log (logRegime α n * n)))))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMLog
