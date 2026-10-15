-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_regime_conditions
-- name    : GDPRDataMarkets.Benchmark.regime_conditions
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:59.889345+00:00
-- url     : https://prove2.me/theorems/1f2c13c7-2653-4d60-8eb7-70b41fe725ec
-- title:
--   Proof of Prop. 2, p. 50 — v^B_M(P₁^B) ≥ c ⇔ c ≤ T₁ (then v^B_M(P₁^B) ≤ 1); eq. (8)'s threshold ≤ 1 ⇔ c ≤ 1 + δμ/(1 + δ), < c ⇔ c > (1 + δσ)/(1 + δμ + δσ)
-- statement:
--   Under the standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$, let $\overline v_1^B=v^B_M(P_1^B)$ be the threshold of eq. (6) at the price $P_1^B$ of eq. (7). Let $v_N(p_8)$ be the threshold $(p_1+(1+\delta)c)/(1+\delta\sigma)$ at the price $p_8$ of eq. (8). Write
--   $$T_1=\frac{2-\delta+2\delta\sigma}{2-\delta+2\delta\mu+2\delta\sigma},\qquad T_2=1+\frac{\delta}{1+\delta}\mu.$$
--   Then:
--   1. $v^B_M(P_1^B)\ge c$ if and only if $c\le T_1$;
--   2. if $c\le T_1$, then $v^B_M(P_1^B)\le 1$;
--   3. $v_N(p_8)\le1$ if and only if $c\le T_2$;
--   4. $v_N(p_8)<c$ if and only if $c>\dfrac{1+\delta\sigma}{1+\delta\mu+\delta\sigma}$.
--
--   These conditions separate the regimes of Proposition 2. In the first, the firm sells the basic good in period 2. In the second, it does not, but some consumers buy in period 1. In the third, nobody buys.
--
--   **Formalization Note.** Only the standing assumptions are needed; Assumption 1 is not used. The theorem also records that $\overline v_1^B$ as defined in the model equals $v^B_M(P_1^B)$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 50, Appendix, proof of Proposition 2, paragraphs after eq. (7) and after eq. (8)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced

namespace GDPRDataMarkets.Benchmark
theorem regime_conditions (P : Params) (hS : P.Standing) :
    vB P (P1B P) = vbar1B P ∧
    (P.c ≤ vbar1B P ↔ P.c ≤ T1 P) ∧
    (P.c ≤ T1 P → vbar1B P ≤ 1) ∧
    (vN P (p8 P) ≤ 1 ↔ P.c ≤ T2 P) ∧
    (vN P (p8 P) < P.c ↔
      (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) < P.c) := by sorry
end GDPRDataMarkets.Benchmark
