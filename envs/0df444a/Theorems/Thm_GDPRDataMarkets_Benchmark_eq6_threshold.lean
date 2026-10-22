-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_eq6_threshold
-- name    : GDPRDataMarkets.Benchmark.eq6_threshold
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:50.742125+00:00
-- url     : https://prove2.me/theorems/831974ea-2578-4058-9069-ad9dff4542c7
-- title:
--   Eq. (6), p. 49 — the first-period purchase threshold (p₁ + c − δp₂)/(1 − δ + δσ) and the solved fixed point with eq. (5)
-- statement:
--   Consider the benchmark model under the standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$, with $\mu=(\kappa_H+\kappa_L)/2$, $\sigma=(\kappa_H-\kappa_L)/2$.
--
--   1. **Threshold.** Let $v\ge0$, let the personalized price be $r(v)=(1+\mu-\sigma)v$, and let the second-period basic price $p_2=p_2(p_1)$ satisfy $p_2+c\le v$. A consumer of valuation $v$ prefers buying in period 1 to waiting, i.e.
--   $$v-p_1-c+\delta\,\mathbb E\big[\max\{(1+\kappa)v-r(v)-c,\,-c\}\big]\ \ge\ \delta\,(v-p_2-c),$$
--   if and only if
--   $$v\ \ge\ \frac{p_1+c-\delta p_2}{1-\delta+\delta\sigma}.$$
--   2. **Fixed point.** If $w=(p_1+c-\delta q)/(1-\delta+\delta\sigma)$ (eq. (6)) and $q=(w-c)/2$ (eq. (5)), then
--   $$w=\frac{2p_1+(2+\delta)c}{2-\delta+2\delta\sigma},\qquad q=\frac{p_1+\delta(1-\sigma)c}{2-\delta+2\delta\sigma}.$$
--
--   These are the equilibrium first-period threshold $v^B_M(p_1)$ and second-period price $p^B_{2M}(p_1)$ in the regime where the firm sells the basic good in period 2.
--
--   **Formalization Note.** The expectation over $\kappa\in\{\kappa_L,\kappa_H\}$ is the average of the two types. The hypothesis $p_2+c\le v$ restricts part 1 to the consumers who would buy the basic good if they waited; this is the region in which the page's inequality, whose right side is $\delta(v-p_2-c)$ rather than $\delta\max\{v-p_2-c,0\}$, is the consumer's comparison. Under the standing assumptions $1-\delta+\delta\sigma>0$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 49, Appendix, proof of Proposition 2, eq. (6) and the solved forms of v^B_M(p₁), p^B_2M(p₁)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced

namespace GDPRDataMarkets.Benchmark
theorem eq6_threshold (P : Params) (hS : P.Standing) :
    (∀ (σ : Profile) (p1 v : ℝ), 0 ≤ v →
        σ.r v = (1 + P.mu - P.sigma) * v → σ.p2 p1 + P.c ≤ v →
        (U1wait P σ p1 v ≤ U1buy P σ p1 v ↔
          (p1 + P.c - P.d * σ.p2 p1) / (1 - P.d + P.d * P.sigma) ≤ v)) ∧
    (∀ p1 w q : ℝ, w = (p1 + P.c - P.d * q) / (1 - P.d + P.d * P.sigma) →
        q = (w - P.c) / 2 → w = vB P p1 ∧ q = qB P p1) := by sorry
end GDPRDataMarkets.Benchmark
