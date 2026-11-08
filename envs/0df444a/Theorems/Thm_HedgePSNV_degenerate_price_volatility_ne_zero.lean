-- Prove2me | Theorems.Thm_HedgePSNV_degenerate_price_volatility_ne_zero
-- name    : HedgePSNV.degenerate_price_volatility_ne_zero
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:57:04.094212+00:00
-- url     : https://prove2.me/theorems/9f1e732f-1691-4119-abd2-da03d4682b8d
-- title:
--   When $Z_T=1$ a.s., $X_t\sigma_t\ne0$ for a.e. $(t,\omega)\in(0,T]\times\Omega$
-- statement:
--   In the standing model of §3.1 of the source (independent Brownian motions $B,\tilde B$, augmented filtration $\mathcal F_t$, asset price $dX_t=X_t(\mu_t\,dt+\sigma_t\,dB_t)$ with $X_0=x_0>0$, $\sigma_t>0$, density process $Z$ of the risk-neutral measure $\mathbb P^M$ in (12)), suppose Assumptions 4 and 5 hold and $Z_T=1$ almost surely. Then for almost every $\omega$,
--
--   $$X_t(\omega)\,\sigma_t(\omega)\ne0\quad\text{for almost every } t\in(0,T].$$
--
--   Role: the integrand $X_t\sigma_t$ of $dX_t=X_t\sigma_t\,dB_t$ must not vanish for $dB$-increments to be rewritten as $dX$-increments; this is the non-degeneracy used when the hedge is built from $dB_t=dX_t/(X_t\sigma_t)$.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, eq. (8), p. 11 (dX_t = X_t(mu_t dt + sigma_t dB_t), sigma_t > 0, X_0 = x_0 > 0: a stochastic exponential, hence nonzero) and eq. (EC.7.3), p. ec23

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem degenerate_price_volatility_ne_zero (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ)) :
    ∀ᵐ ω ∂M.P, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) p.T →
      M.X u.toNNReal ω * M.σ u.toNNReal ω ≠ 0 := by sorry

end HedgePSNV
