-- Prove2me | Theorems.Thm_HedgePSNV_payoff_simple_integral_density
-- name    : HedgePSNV.payoff_simple_integral_density
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T21:55:58.0702+00:00
-- url     : https://prove2.me/theorems/708ee6e7-89c6-41ee-b8b3-37687c1ef49b
-- title:
--   The newsvendor payoff $H_T(P,R)$ is an $L^2$ limit of constants plus simple integrals against $B$ and $\tilde B$
-- statement:
--   In the standing model of §3.1 of the source (independent Brownian motions $B,\tilde B$, augmented filtration $\mathcal F_t$, asset price $dX_t=X_t(\mu_t\,dt+\sigma_t\,dB_t)$ with $X_0=x_0>0$, $\sigma_t>0$, density process $Z$ of the risk-neutral measure $\mathbb P^M$ in (12)), suppose $\mathbb E[((C_T)^-)^2]<\infty$. Then for all $P,R$ and every $\eta>0$ there are $n\ge1$, a constant $c$ and coefficients $Y_k,Z_k$ that are bounded and $\mathcal F_{t_k}$-measurable, $t_k=kT/n$, such that
--
--   $$\mathbb E\Big[\Big(H_T(P,R)-c-\sum_{k<n}Y_k\,(B_{t_{k+1}}-B_{t_k})-\sum_{k<n}Z_k\,(\tilde B_{t_{k+1}}-\tilde B_{t_k})\Big)^2\Big]\le\eta .$$
--
--   Role: this is the $L^2$ form of the martingale representation of $H_T(P,R)$ on the Brownian filtration, used to show that the residual risk $\int_0^T\mathbb E[\delta_t^2]dt$ is approached by admissible hedges.
-- source:
--   Wang, Yao, Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, https://arxiv.org/abs/2201.01026, Proposition EC.3(i) and its proof, pp. ec23-ec24 (martingale representation dM_t = Gamma_t dB_t + Lambda_t d~B_t, citing Pham 2009); standard form: Karatzas and Shreve, Brownian Motion and Stochastic Calculus (1991), Theorem 3.4.15 with Lemma 3.2.4 (simple integrands are dense)

import Mathlib
import Definitions.Def_HedgePSNV_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

theorem payoff_simple_integral_density (p : Params) {Ω : Type*} [MeasurableSpace Ω] (M : Model p Ω)
    (hM : M.Standing) (hL2 : M.NegPartL2) (P R : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ n : ℕ, 0 < n ∧ ∃ c : ℝ, ∃ Y Z : ℕ → Ω → ℝ, ∃ C : ℝ,
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Y k)) ∧ (∀ k ω, |Y k ω| ≤ C) ∧
      (∀ k, StronglyMeasurable[M.F (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0)))] (Z k)) ∧ (∀ k ω, |Z k ω| ≤ C) ∧
      ∫ ω, (M.H P R ω - c - ∑ k ∈ Finset.range n, Y k ω * (M.B ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.B (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω) -
        ∑ k ∈ Finset.range n, Z k ω * (M.Bt ((((k + 1 : ℕ) : ℝ≥0)) * (p.T / (n : ℝ≥0))) ω - M.Bt (((k : ℕ) : ℝ≥0) * (p.T / (n : ℝ≥0))) ω)) ^ 2 ∂M.P ≤ η := by sorry

end HedgePSNV
