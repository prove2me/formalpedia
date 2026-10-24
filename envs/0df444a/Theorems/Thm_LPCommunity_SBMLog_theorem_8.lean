-- Prove2me | Theorems.Thm_LPCommunity_SBMLog_theorem_8
-- name    : LPCommunity.SBMLog.theorem_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:21.492783+00:00
-- url     : https://prove2.me/theorems/c03e12d5-c06a-44db-b967-b38ae8eb33fc
-- title:
--   Theorem 8, p. 18 — in the logarithmic-degree SBM the LP relaxation fails to recover the planted bisection w.h.p.
-- statement:
--   Let $n$ be even, $G\sim\mathcal G_{n,p,q}$ be drawn from the stochastic block model with a uniformly random planted bisection $V_1,V_2$, and suppose the degrees are logarithmic:
--   $$
--   p=\alpha\frac{\log n}{n},\qquad q=\beta\frac{\log n}{n},\qquad \alpha>\beta>0.
--   $$
--   Then, with high probability, the metric LP relaxation (LP-P) of the minimum bisection problem fails to recover the planted bisection:
--   $$
--   \lim_{n\to\infty}\ \mathbb P\big[\bar x \text{ is not the unique optimal solution of (LP-P) for } G\big]=1,
--   $$
--   where $\bar x$ is the cut vector of $V_1,V_2$.
--
--   Together with the information-theoretic threshold $\sqrt\alpha-\sqrt\beta>\sqrt2$ of Abbe, Bandeira and Hall, above which the minimum bisection problem and its SDP relaxation do recover, this shows that the LP relaxation is strictly weaker than the SDP relaxation in the logarithmic regime: it fails for every $\alpha>\beta>0$.
--
--   **Formalization Note** The theorem prints only $\alpha,\beta>0$; $\alpha>\beta$ is the SBM's standing assumption $p>q$ (p. 13) and that of (21), and Proposition 19, used in the proof, assumes it. The limit runs along even $n=2m$. (LP-P) is the metric relaxation with variables in $\mathbb R^{\binom n2}$ and no box constraints.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 18, Theorem 8

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMLog_RandomGraphs

namespace LPCommunity.SBMLog

/-- Theorem 8 (arXiv:2006.03213v2, p. 18). In the logarithmic-degree SBM `G_{n,p,q}` with
`p = α log n / n`, `q = β log n / n` and `α > β > 0`, the LP relaxation (LP-P) fails to recover the
planted bisection with high probability (along even `n = 2m`). -/
theorem theorem_8 (α β : ℝ) (hβ : 0 < β) (hαβ : β < α) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (logRegime α (2 * m)) (logRegime β (2 * m))
        (fun V1 G => ¬ LPCommunity.LPRecovery.LPRecovers G V1))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMLog
