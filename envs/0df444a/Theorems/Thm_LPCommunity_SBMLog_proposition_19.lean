-- Prove2me | Theorems.Thm_LPCommunity_SBMLog_proposition_19
-- name    : LPCommunity.SBMLog.proposition_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:11.624193+00:00
-- url     : https://prove2.me/theorems/bada282b-fd93-4c03-9d28-1706984b2cb9
-- title:
--   Proposition 19, p. 30 — in the logarithmic-degree SBM, ρ_avg and ρ_max are (1 ± ϵ) log n/log log n w.h.p.
-- statement:
--   Let $p=\alpha\frac{\log n}{n}$ and $q=\beta\frac{\log n}{n}$ with $\alpha>\beta>0$ and $\frac{\alpha+\beta}{2}>1$, and let $G\sim\mathcal G_{n,p,q}$. Then for every $\epsilon>0$,
--   $$
--   \lim_{n\to\infty}\mathbb P\left[(1-\epsilon)\frac{\log n}{\log\log n}\le\rho_{\mathrm{avg}}(G)\le\rho_{\max}(G)\le(1+\epsilon)\frac{\log n}{\log\log n}\right]=1.
--   $$
--
--   Here $\rho_{\max}(G)$ is the diameter and $\rho_{\mathrm{avg}}(G)=\frac{2}{n^2}\sum_{i<j}\rho_G(i,j)$ the average distance. This is the distance input of Theorem 8: on this event the distance-based non-recovery criterion for the LP relaxation applies.
--
--   **Formalization Note** $n=2m$ runs over the even integers. $\rho_{\mathrm{avg}}$ and $\rho_{\max}$ are compared in $[0,\infty]$, so a disconnected sample never satisfies the event. The middle inequality holds for every graph and is kept because it is printed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 30, Proposition 19

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

namespace LPCommunity.SBMLog

/-- Proposition 19 (arXiv:2006.03213v2, p. 30). For `p = α log n / n`, `q = β log n / n` with
`α > β > 0` and `(α + β)/2 > 1`, and `G ∼ G_{n,p,q}`, for every `ε > 0`, with probability tending
to `1` (along even `n = 2m`),
`(1 − ε) log n / log log n ≤ ρ_avg(G) ≤ ρ_max(G) ≤ (1 + ε) log n / log log n`. -/
theorem proposition_19 (α β : ℝ) (hβ : 0 < β) (hαβ : β < α) (hsum : 1 < (α + β) / 2)
    (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m)) (fun _ G =>
        ENNReal.ofReal ((1 - ε) * (Real.log (2 * m : ℕ) / Real.log (Real.log (2 * m : ℕ)))) ≤ LPCommunity.LPFail.rhoAvg G ∧
        LPCommunity.LPFail.rhoAvg G ≤ ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ENNReal) ∧
        ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ENNReal) ≤
          ENNReal.ofReal ((1 + ε) * (Real.log (2 * m : ℕ) / Real.log (Real.log (2 * m : ℕ))))))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMLog
