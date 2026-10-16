-- Prove2me | Theorems.Thm_LPCommunity_SBMLog_proposition_13
-- name    : LPCommunity.SBMLog.proposition_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:27.272148+00:00
-- url     : https://prove2.me/theorems/72894b07-bbff-4967-92c7-3bd656f4aa7e
-- title:
--   Proposition 13, p. 29 — the diameter of G_{n,α log n/n} is (1 ± ϵ) log n/log log n w.h.p.
-- statement:
--   Let $\alpha>1$, $p=\alpha\frac{\log n}{n}$, and $G\sim\mathcal G_{n,p}$ be an Erdős–Rényi graph. Write $\rho_{\max}(G)$ for the diameter of $G$ ($+\infty$ if $G$ is disconnected). Then for every $\epsilon>0$,
--   $$
--   \lim_{n\to\infty}\mathbb P\left[\rho_{\max}(G)\in\left((1-\epsilon)\frac{\log n}{\log\log n},\ (1+\epsilon)\frac{\log n}{\log\log n}\right)\right]=1.
--   $$
--
--   The paper derives it from Theorem 4 of Chung and Lu (2001) on the diameter of sparse random graphs, using $\log(pn)=\log\alpha+\log\log n\sim\log\log n$. It is the Erdős–Rényi input to the diameter bound for the logarithmic-degree SBM.
--
--   **Formalization Note** The interval is open, as printed. $\rho_{\max}$ is compared in $[0,\infty]$, so a disconnected sample never satisfies the event. For the finitely many $n$ with $\log\log n\le0$ the bounds take Lean's default values; this does not affect the limit.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 29, Proposition 13

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

namespace LPCommunity.SBMLog

/-- Proposition 13 (arXiv:2006.03213v2, p. 29). For `p = α log n / n` with `α > 1` and
`G ∼ G_{n,p}`, for every `ε > 0` the diameter `ρ_max(G)` lies in the open interval
`((1 − ε) log n / log log n, (1 + ε) log n / log log n)` with probability tending to `1`. -/
theorem proposition_13 (α : ℝ) (hα : 1 < α) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (logRegime α n) (fun G =>
        ENNReal.ofReal ((1 - ε) * (Real.log n / Real.log (Real.log n))) < ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ENNReal) ∧
        ((LPCommunity.LPFail.rhoMax G : ℕ∞) : ENNReal) < ENNReal.ofReal ((1 + ε) * (Real.log n / Real.log (Real.log n)))))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMLog
