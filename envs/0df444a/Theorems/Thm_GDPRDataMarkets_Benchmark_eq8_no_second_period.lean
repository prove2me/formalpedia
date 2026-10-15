-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_eq8_no_second_period
-- name    : GDPRDataMarkets.Benchmark.eq8_no_second_period
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:57.131679+00:00
-- url     : https://prove2.me/theorems/8af59215-5245-44a6-8930-fe5b11535ce2
-- title:
--   Eq. (8), p. 50 — without second-period sales the threshold is (p₁ + (1 + δ)c)/(1 + δσ) and the optimal first-period price is eq. (8)
-- statement:
--   Consider the benchmark model under the standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$, in the regime where no first-period non-buyer buys in period 2.
--
--   1. **Threshold.** Let $v\ge0$ and $r(v)=(1+\mu-\sigma)v$. Buying in period 1 gives nonnegative expected utility,
--   $$v-p_1-c+\delta\,\mathbb E\big[\max\{(1+\kappa)v-r(v)-c,\,-c\}\big]\ \ge\ 0,$$
--   if and only if
--   $$v\ \ge\ v_N(p_1)=\frac{p_1+(1+\delta)c}{1+\delta\sigma}.$$
--   2. **Price.** The first-period objective $\pi_N(p_1)=\int_{v_N(p_1)}^{1}\big(p_1+\delta(1+\mu-\sigma)v\big)\,dv$ satisfies $\pi_N(p_1)\le\pi_N(p_8)$ for all real $p_1$, where
--   $$p_8=\frac{(1+\delta\sigma)^2-(1+\delta)(1+\delta+\delta\mu)c}{2+\delta+\delta\mu+\delta\sigma}.$$
--
--   This is the first-period price of case B of Proposition 2 when $c>(1+\delta\sigma)/(1+\delta\mu+\delta\sigma)$.
--
--   **Formalization Note.** $\pi_N$ is a concave quadratic in $p_1$, so the claim is global over $\mathbb R$. The expectation over $\kappa$ is the average of the two types.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 50, Appendix, proof of Proposition 2, eq. (8) and the display before it

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced

namespace GDPRDataMarkets.Benchmark
theorem eq8_no_second_period (P : Params) (hS : P.Standing) :
    (∀ (σ : Profile) (p1 v : ℝ), 0 ≤ v → σ.r v = (1 + P.mu - P.sigma) * v →
        (0 ≤ U1buy P σ p1 v ↔ vN P p1 ≤ v)) ∧
    (∀ p1 : ℝ, piN P p1 ≤ piN P (p8 P)) := by sorry
end GDPRDataMarkets.Benchmark
