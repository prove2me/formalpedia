-- Prove2me | Theorems.Thm_HedgePSNV_degenerate_simple_integrals_attainable
-- name    : HedgePSNV.degenerate_simple_integrals_attainable
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:56:31.381749+00:00
-- url     : https://prove2.me/theorems/421327c9-d278-41a4-bdb2-e4f69ac98092
-- title:
--   When $Z_T=1$ and $X\sigma\ne0$, simple $dB$-integrals are $L^2$-attainable by admissible gains $\chi_T$
-- statement:
--   In the standing model of §3.1 of the source (independent Brownian motions $B,\tilde B$, augmented filtration $\mathcal F_t$, asset price $dX_t=X_t(\mu_t\,dt+\sigma_t\,dB_t)$ with $X_0=x_0>0$, $\sigma_t>0$, density process $Z$ of the risk-neutral measure $\mathbb P^M$ in (12)), suppose Assumptions 4 and 5 hold, $Z_T=1$ almost surely, and $X_t\sigma_t\ne0$ for almost every $(t,\omega)\in(0,T]\times\Omega$. Then for every $n\ge1$, every family $Y_k$ of bounded $\mathcal F_{t_k}$-measurable coefficients ($t_k=kT/n$) and every $\eta>0$ there is an admissible strategy $(\theta,\chi)\in\mathcal A_X$ with
--
--   $$\mathbb E\Big[\Big(\chi_T+\sum_{k<n}Y_k\,(B_{t_{k+1}}-B_{t_k})\Big)^2\Big]\le\eta .$$
--
--   Role: it converts the $dB$-part of the representation of $H_T$ into trading gains $\int\theta\,dX$ (using $dB_t=dX_t/(X_t\sigma_t)$ when $\mathbb P^M=\mathbb P$), which gives the upper bound for $B(m,P,R)$ in the degenerate case.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, proof of Lemma 1 and Theorem 1, p. ec27 ('dB^M_t is related to dX_t based on the dynamics of X_t in P^M; see (EC.7.3)'), eq. (EC.7.3), p. ec23, admissible set A_X (EC.7.15), p. ec29, with Z_T = 1 (P^M = P)

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem degenerate_simple_integrals_attainable (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (h4 : M.Assumption4) (h5 : M.Assumption5)
    (hdeg : M.Z p.T =ᵐ[M.P] fun _ => (1 : ℝ))
    (hS3 : ∀ᵐ ω ∂M.P, ∀ᵐ u ∂volume, u ∈ Set.Ioc (0 : ℝ) p.T →
      M.X u.toNNReal ω * M.σ u.toNNReal ω ≠ 0) :
    ∀ n : ℕ, 0 < n → ∀ (Y : ℕ → Ω → ℝ) (C : ℝ),
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Y k)) → (∀ k ω, |Y k ω| ≤ C) →
      ∀ η : ℝ, 0 < η → ∃ θχ ∈ M.AX,
      ∫ ω, (θχ.2 p.T ω + ∑ k ∈ Finset.range n, Y k ω * (M.B ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.B (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω)) ^ 2 ∂M.P ≤ η := by sorry

end HedgePSNV
