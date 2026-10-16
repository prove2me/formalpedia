-- Prove2me | Theorems.Thm_LPCommunity_SBMDense_theorem_7
-- name    : LPCommunity.SBMDense.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:38:33.542707+00:00
-- url     : https://prove2.me/theorems/34750d49-f4cf-417a-a32e-a6df2a881b42
-- title:
--   Theorem 7, pp. 15–16 — under any of (22)–(25) the metric LP fails w.h.p. to recover the planted bisection in the dense SBM
-- statement:
--   Let $p=\alpha n^{-\omega}$ and $q=\beta n^{-\omega}$ with $\alpha>\beta>0$ and $\omega\in[0,1)$, with $\alpha,\beta\in(0,1)$ if $\omega=0$, and let $(V_1,G)\sim\mathcal G_{n,p,q}$. Suppose that one of the following holds:
--
--   1. $\omega=0$ and $\displaystyle\beta>\max\Big\{\frac{3-\alpha-\sqrt{(3-\alpha)^2-4\alpha}}{2},\ 2\alpha-1\Big\}$; (22)
--   2. $\omega\in(0,1)$ with $\frac1{1-\omega}\notin\mathbb N$ and $\displaystyle\beta>\frac{1}{2\lceil\frac1{1-\omega}\rceil-1}\cdot\alpha$; (23)
--   3. $\omega=\frac12$ and $\displaystyle\beta>\max\Big\{\frac{1-2e^{-\alpha^2}}{2-e^{-\alpha^2}},\ \frac{1}{3+2e^{-\alpha^2}}\Big\}\cdot\alpha$; (24)
--   4. $\omega\in(0,1)$ with $\frac1{1-\omega}\in\mathbb N\setminus\{2\}$ and $\displaystyle\beta>\frac{1}{2\cdot\frac1{1-\omega}-1+2\exp(-\alpha^{\frac1{1-\omega}})}\cdot\alpha$. (25)
--
--   Then, with high probability, the metric relaxation (LP-P) fails to recover the planted bisection:
--
--   $$
--   \lim_{n\to\infty}\mathbb P\big[\bar x(V_1)\text{ is not the unique optimal solution of (LP-P) for }G\big]=1.
--   $$
--
--   Together with Theorem 6, Condition 1 brackets the region of constant $(p,q)$ in which the LP relaxation recovers the planted bisection in the very dense regime.
--
--   **Formalization Note** The theorem prints only $\alpha,\beta>0$; the hypothesis $\alpha>\beta$ is added as the stochastic block model's standing assumption $p>q$ (§4, p. 13), which Proposition 18 and (26), used in the proof, also assume. The limit runs over even $n=2m$, the probability is over both the uniformly random planted bisection and the edges, and "fails to recover" is evaluated at the drawn bisection. Edge probabilities are clamped into $[0,1]$ (relevant only for finitely many $n$).
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, pp. 15–16, Theorem 7, (22)–(25)

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting
import Definitions.Def_LPCommunity_SBMDense_RandomGraphs
import Definitions.Def_LPCommunity_SBMDense_Thresholds

namespace LPCommunity.SBMDense

theorem theorem_7 (α β ω : ℝ) (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α) (hω0 : 0 ≤ ω) (hω1 : ω < 1)
    (hdense : ω = 0 → α < 1 ∧ β < 1)
    (hcond : Cond22 α β ω ∨ Cond23 α β ω ∨ Cond24 α β ω ∨ Cond25 α β ω) :
    Filter.Tendsto
      (fun m : ℕ => LPCommunity.SBMRecovery.sbmProb (2 * m) (denseRegime α ω (2 * m)) (denseRegime β ω (2 * m))
        (fun V1 G => ¬ LPCommunity.LPRecovery.LPRecovers G V1))
      Filter.atTop (nhds 1) := by sorry

end LPCommunity.SBMDense
