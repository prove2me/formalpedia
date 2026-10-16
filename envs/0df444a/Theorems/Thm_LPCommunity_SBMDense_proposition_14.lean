-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_proposition_14
-- name    : LPCommunity.SBMDense.proposition_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:19.057652+00:00
-- url     : https://prove2.me/theorems/183efda2-c7b5-4ae0-9591-8902a8c7c442
-- title:
--   Proposition 14, p. 29 (Shimizu) — the average distance of $\mathcal G_{n,\alpha n^{-\omega}}$ concentrates at $\mu(\omega,\alpha)$
-- statement:
--   Let $\omega\in(0,1)$ and $\alpha>0$, and let $G\sim\mathcal G_{n,p}$ with $p=\alpha n^{-\omega}$. Define
--
--   $$
--   \mu=\mu(\omega,\alpha)=\Big\lceil\frac{1}{1-\omega}\Big\rceil+\mathbf 1\Big\{\frac1{1-\omega}\in\mathbb N\Big\}\exp\big(-\alpha^{\frac1{1-\omega}}\big).
--   $$
--
--   Then for every $\epsilon>0$,
--
--   $$
--   \lim_{n\to\infty}\mathbb P\big[\rho_{\mathrm{avg}}(G)\in((1-\epsilon)\mu,(1+\epsilon)\mu)\big]=1.
--   $$
--
--   This is Theorem 1 of Shimizu, restated by the paper in the form it needs; with Proposition 11 it gives the lower bounds on $\rho_{\mathrm{avg}}$ in Propositions 17 and 18.
--
--   **Formalization Note** $\rho_{\mathrm{avg}}(G)$ takes values in $[0,\infty]$ and the endpoints $(1\pm\epsilon)\mu$ are embedded with `ENNReal.ofReal` (a negative endpoint becomes $0$); the open upper bound excludes $\rho_{\mathrm{avg}}=+\infty$, i.e. disconnected graphs.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 29, Proposition 14 (Theorem 1 of [38], Shimizu)

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs
import Definitions.Def_LPCommunity_SBMDense_Thresholds

namespace LPCommunity.SBMDense

theorem proposition_14 (α ω : ℝ) (hα : 0 < α) (hω0 : 0 < ω) (hω1 : ω < 1) (ε : ℝ) (hε : 0 < ε) :
    Filter.Tendsto
      (fun n : ℕ => LPCommunity.SBMRecovery.erProb n (denseRegime α ω n)
        (fun G => ENNReal.ofReal ((1 - ε) * mu ω α) < LPCommunity.LPFail.rhoAvg G ∧
          LPCommunity.LPFail.rhoAvg G < ENNReal.ofReal ((1 + ε) * mu ω α)))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
