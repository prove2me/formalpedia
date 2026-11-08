-- Prove2me | Theorems.Thm_HedgePSNV_degenerate_price_martingale
-- name    : HedgePSNV.degenerate_price_martingale
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:55:13.564684+00:00
-- url     : https://prove2.me/theorems/6e708062-9882-497d-a12f-74d6b875ae7c
-- title:
--   When $Z_T=1$ a.s., the asset price $X$ is a square-integrable $\mathbb P$-martingale on $[0,T]$
-- statement:
--   In the standing model of §3.1 of the source (independent Brownian motions $B,\tilde B$, augmented filtration $\mathcal F_t$, asset price $dX_t=X_t(\mu_t\,dt+\sigma_t\,dB_t)$ with $X_0=x_0>0$, $\sigma_t>0$, density process $Z$ of the risk-neutral measure $\mathbb P^M$ in (12)), suppose Assumptions 4 and 5 hold and $Z_T=1$ almost surely, so that $\mathbb P^M=\mathbb P$. Then $X$ is a martingale on $[0,T]$ with respect to $(\mathcal F_t)$ under $\mathbb P$ and each $X_t$, $t\le T$, is square integrable:
--
--   $$\mathbb E[X_t\mid\mathcal F_s]=X_s\quad(0\le s\le t\le T),\qquad \mathbb E[X_t^2]<\infty\quad(t\le T).$$
--
--   Role: in the degenerate case the hedging problem is posed under $\mathbb P$ itself, and the variance bounds for $H_T+\chi_T$ need $X$ to be a square-integrable $\mathbb P$-martingale.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, eq. (EC.7.3), p. ec23, and the proof of Lemma 1 (EC.7.2), p. ec26 ('X_t ... is a (local) martingale under P^M', dX_t = sigma_t X_t dB^M_t), with Z_T = 1 (P^M = P) and Assumption 4, p. 11

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem degenerate_price_martingale (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) :
    IsMartingaleOn p.T M.F M.P M.X ∧ ∀ t : ℝ≥0, t ≤ p.T → MemLp (M.X t) 2 M.P := by sorry

end HedgePSNV
