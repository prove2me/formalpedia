-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_eq5_second_period_price
-- name    : GDPRDataMarkets.Benchmark.eq5_second_period_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:15.58328+00:00
-- url     : https://prove2.me/theorems/14dc0f9a-3603-4e64-8f9e-51def173fada
-- title:
--   Eq. (5), p. 49 — given first-period buyers v ≥ w with c ≤ w ≤ 1, the optimal second-period basic price is (w − c)/2
-- statement:
--   Consider the benchmark model, under the standing assumptions $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$. Fix a strategy profile and a first-period price $p_1$. Suppose the first-period buyers at $p_1$ are exactly the consumers with $v\ge w$, for some threshold $w$ with
--   $$c\le w\le 1.$$
--   In period 2 a first-period non-buyer buys the basic good at price $q$ iff $v-q-c\ge0$. Then the firm's second-period profit is maximized over all real $q$ at
--   $$q=\frac{w-c}{2}.$$
--   This is eq. (5): $p^B_{2M}(p_1)=(v^B_M(p_1)-c)/2$.
--
--   Together with eq. (6) it pins down the fixed point between the consumers' first-period threshold and the firm's second-period price.
--
--   **Formalization Note.** The second-period profit is the integral of the personalized revenue over the first-period buyers plus $q$ times the Lebesgue measure of the set of non-buyers who buy the basic good. The paper writes this mass as $v^B_M(p_1)-(p_2+c)$, which is wrong for $q<-c$. The theorem compares the true profits for every real $q$. The hypothesis $w\le1$ is the paper's "$v^B_M(P_1^B)\le1$"; $c\le w$ is its standing assumption of that regime ($v^B_M\ge c$).
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), p. 49, Appendix, proof of Proposition 2, eq. (5)

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model

namespace GDPRDataMarkets.Benchmark
theorem eq5_second_period_price (P : Params) (hS : P.Standing) (σ : Profile) (p1 w : ℝ)
    (hthr : ∀ v ∈ Set.Icc (0 : ℝ) 1, (σ.buy p1 v = true ↔ w ≤ v))
    (hcw : P.c ≤ w) (hw1 : w ≤ 1) :
    ∀ q : ℝ, profit2 P σ p1 q ≤ profit2 P σ p1 ((w - P.c) / 2) := by sorry
end GDPRDataMarkets.Benchmark
