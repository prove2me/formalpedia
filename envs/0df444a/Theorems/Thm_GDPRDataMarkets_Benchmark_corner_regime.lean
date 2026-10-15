-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_corner_regime
-- name    : GDPRDataMarkets.Benchmark.corner_regime
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:58.565987+00:00
-- url     : https://prove2.me/theorems/b09c7229-1702-4c67-bcdb-1bee54fb4316
-- title:
--   Proof of Prop. 2, p. 51 — the corner price δ(σ − 1)c with v^B_M = c, and the combined definitions of v₂^B and P₂^B
-- statement:
--   Under the standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$, let $p_c=\delta(\sigma-1)c$. Let $v^B_M$, $\pi_S$ (eqs. (6)–(7)), $v_N$, $\pi_N$, $p_8$ (eq. (8)) and $T_1$ be as in the previous milestones, and let $X=\frac{1+\delta\sigma}{1+\delta\mu+\delta\sigma}$.
--
--   1. Both thresholds equal $c$ at the corner price: $v_N(p_c)=c$ and $v^B_M(p_c)=c$.
--   2. If $T_1<c\le X$, then $\pi_N$ is maximized at $p_c$ among all $p_1\le p_c$, $\pi_S$ is maximized at $p_c$ among all $p_1\ge p_c$, and
--   $$P_2^B=\delta(\sigma-1)c,\qquad v_2^B=c.$$
--   3. If $c>X$, then $P_2^B=p_8$ and $v_2^B=v_N(p_8)$.
--
--   Here
--   $$v_2^B=\min\Big\{\frac{1+\delta\sigma+(1+\delta)c}{2+\delta+\delta\mu+\delta\sigma},\,c\Big\},\qquad P_2^B=\min\Big\{\frac{(1+\delta\sigma)^2-(1+\delta)(1+\delta+\delta\mu)c}{2+\delta+\delta\mu+\delta\sigma},\,\delta(\sigma-1)c\Big\}.$$
--
--   In the middle range the firm prices at the kink where the two regimes meet. Taken together, the two cases give case B of Proposition 2.
--
--   **Formalization Note.** The page states that the firm sets $p_1$ with $v^B_M(p_1)=c$; the theorem formalizes this as optimality of the corner on each side of the kink, which is what makes it the maximizer of the piecewise objective.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 51, Appendix, proof of Proposition 2, last paragraph (definitions of v₂^B and P₂^B)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model
import Definitions.Def_GDPRDataMarkets_Benchmark_Reduced

namespace GDPRDataMarkets.Benchmark
theorem corner_regime (P : Params) (hS : P.Standing) :
    vN P (P.d * (P.sigma - 1) * P.c) = P.c ∧
    vB P (P.d * (P.sigma - 1) * P.c) = P.c ∧
    (T1 P < P.c → P.c ≤ (1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) →
      (∀ p1 : ℝ, p1 ≤ P.d * (P.sigma - 1) * P.c →
          piN P p1 ≤ piN P (P.d * (P.sigma - 1) * P.c)) ∧
      (∀ p1 : ℝ, P.d * (P.sigma - 1) * P.c ≤ p1 →
          piS P p1 ≤ piS P (P.d * (P.sigma - 1) * P.c)) ∧
      P2B P = P.d * (P.sigma - 1) * P.c ∧ v2B P = P.c) ∧
    ((1 + P.d * P.sigma) / (1 + P.d * P.mu + P.d * P.sigma) < P.c →
      P2B P = p8 P ∧ v2B P = vN P (p8 P)) := by sorry
end GDPRDataMarkets.Benchmark
