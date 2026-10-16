-- Prove2me | Theorems.Thm_LPCommunity_SBMLog_abh_threshold
-- name    : LPCommunity.SBMLog.abh_threshold
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:12.496013+00:00
-- url     : https://prove2.me/theorems/f55d980c-0665-44fc-b202-d420fe014f14
-- title:
--   §4, p. 14 (result of [2]) — the minimum bisection recovers w.h.p. iff √α − √β > √2 (strict cases)
-- statement:
--   Consider the stochastic block model $G\sim\mathcal G_{n,p,q}$ on $n$ nodes ($n$ even) with planted bisection $V_1,V_2$ and logarithmic degree
--   $$
--   p=\alpha\frac{\log n}{n},\qquad q=\beta\frac{\log n}{n},\qquad \alpha>\beta>0.
--   $$
--   Let $P_n$ be the probability that the minimum bisection problem recovers the planted bisection, i.e. that $V_1,V_2$ is the unique bisection of minimum cost in $G$. Then:
--
--   1. if $\sqrt\alpha-\sqrt\beta>\sqrt2$, then $P_n\to1$ as $n\to\infty$ (recovery with high probability);
--   2. if $\sqrt\alpha-\sqrt\beta<\sqrt2$, then $P_n\not\to1$ (no recovery with high probability).
--
--   This is the information-theoretic threshold of Abbe, Bandeira and Hall (2016), as stated on p. 14 of the paper. It is used in the proof of Theorem 8 for the range $(\alpha+\beta)/2\le 1$.
--
--   **Formalization Note** The printed "if and only if" also covers the boundary $\sqrt\alpha-\sqrt\beta=\sqrt2$ (asserting no recovery with high probability there); that case is not proved in the paper and is left out, so only the two strict implications are posed. $\alpha>\beta$ is the standing assumption $p>q$ of the SBM (p. 13) and of (21). The limit runs along even $n=2m$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 14, §4 (result of [2]: Abbe, Bandeira, Hall, Exact recovery in the stochastic block model, IEEE Trans. Inf. Theory 62 (2016))

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

namespace LPCommunity.SBMLog

/-- §4, p. 14 (the result of Abbe–Bandeira–Hall [2], as the paper states it). In the
logarithmic-degree SBM with `p = α log n / n`, `q = β log n / n`, `α > β > 0`: if
`√α − √β > √2` the minimum bisection problem recovers the planted bisection with high
probability, and if `√α − √β < √2` it does not. The boundary `√α − √β = √2` is not posed. -/
theorem abh_threshold (α β : ℝ) (hβ : 0 < β) (hαβ : β < α) :
    (Real.sqrt 2 < Real.sqrt α - Real.sqrt β →
      Filter.Tendsto
        (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
          (fun V1 G => LPCommunity.MinBisect.MinBisectRecovers G V1))
        Filter.atTop (nhds 1)) ∧
    (Real.sqrt α - Real.sqrt β < Real.sqrt 2 →
      ¬ Filter.Tendsto
        (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
          (fun V1 G => LPCommunity.MinBisect.MinBisectRecovers G V1))
        Filter.atTop (nhds 1)) := by sorry

end LPCommunity.SBMLog
