-- Prove2me | Theorems.Thm_GDPRDataMarkets_Benchmark_proposition_2
-- name    : GDPRDataMarkets.Benchmark.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T22:59:41.634264+00:00
-- url     : https://prove2.me/theorems/68eb3746-66fa-429c-9b39-869287dda0d3
-- title:
--   Proposition 2 — without privacy rights the monopoly equilibrium in the three regimes c ≤ T₁, T₁ < c < 1 + δμ/(1 + δ), c ≥ 1 + δμ/(1 + δ)
-- statement:
--   Consider the monopoly market without privacy rights. Every first-period purchase reveals the buyer's valuation $v$ to the firm and exposes her to the breach cost $c$ in both periods, since the data cannot be erased. In period 2 the firm offers each past buyer the personalized good at $r(v)$, and offers first-period non-buyers the basic good at $p_2$. Valuations are uniform on $[0,1]$, $\kappa\in\{\kappa_L,\kappa_H\}$ with probability $1/2$ each, and $\mu=(\kappa_H+\kappa_L)/2$, $\sigma=(\kappa_H-\kappa_L)/2$. Assume $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$ and Assumption 1, $\mu\ge\max\{(3+\delta)\sigma,\ \tfrac12+(2+\delta)\sigma\}$.
--
--   Let $T_1=\frac{2-\delta+2\delta\sigma}{2-\delta+2\delta\mu+2\delta\sigma}$ and $T_2=1+\frac{\delta}{1+\delta}\mu$.
--
--   **A.** If $c\le T_1$, there is an equilibrium with $p^B_{1M}=P_1^B$ and second-period basic price $p^B_{2M}=\big[P_1^B+\delta(1-\sigma)c\big]/(2-\delta+2\delta\sigma)$, in which:
--   1. consumers with $v\ge\overline v_1^B$ buy in period 1 and buy the personalized good in period 2 at $r^B_M(v)=(1+\mu-\sigma)v$;
--   2. consumers with $\overline v_1^B>v\ge\underline v_1^B$ do not buy in period 1 but buy the basic good in period 2;
--   3. consumers with $v<\underline v_1^B$ buy in neither period.
--
--   **B.** If $T_1<c<T_2$, there is an equilibrium with $p^B_{1M}=P_2^B$ in which:
--   1. consumers with $v\ge v_2^B$ buy in period 1 and buy the personalized good in period 2 at $r^B_M(v)=(1+\mu-\sigma)v$;
--   2. consumers with $v<v_2^B$ buy in neither period.
--
--   **C.** If $c\ge T_2$, there is an equilibrium in which no consumer buys in either period.
--
--   The constants are
--   $$P_1^B=\frac{(2-\delta+2\delta\sigma)^2-[4+4\delta-\delta^2+2\delta^2\sigma+2\delta(2+\delta)\mu]c}{2(4-\delta+2\delta\mu+2\delta\sigma)},\qquad \overline v_1^B=\frac{2P_1^B+(2+\delta)c}{2-\delta+2\delta\sigma},\qquad \underline v_1^B=p^B_{2M}+c,$$
--   $$v_2^B=\min\Big\{\frac{1+\delta\sigma+(1+\delta)c}{2+\delta+\delta\mu+\delta\sigma},c\Big\},\qquad P_2^B=\min\Big\{\frac{(1+\delta\sigma)^2-(1+\delta)(1+\delta+\delta\mu)c}{2+\delta+\delta\mu+\delta\sigma},\delta(\sigma-1)c\Big\}.$$
--
--   Here an equilibrium satisfies four conditions:
--   1. the personalized price is revenue-maximizing for every valuation;
--   2. after every first-period price, the second-period basic price maximizes second-period profit given the consumers' first-period choices;
--   3. after every first-period price, every consumer's first-period choice is optimal;
--   4. the first-period price maximizes the firm's total discounted profit over all real prices.
--
--   The proposition is the benchmark against which the paper measures the effect of GDPR-style privacy rights. Without them consumers who buy are locked in and fully charged for personalization. The market becomes "now or never" once the breach cost exceeds $T_1$, and it closes completely once $c\ge T_2$.
--
--   **Formalization Note.** The statement asserts existence, not uniqueness, as the paper does. Profits are integrals over the consumers' optimal choices, not the paper's reduced closed forms. "Buys the personalized good in period 2" is encoded as $r(v)\le(1+\kappa)v$ for both types, using the convention that an indifferent consumer buys. "Buys the basic good in period 2" is $p_2+c\le v$, and "does not" is $v<p_2+c$. $P_1^B$ is eq. (7) with the page's stray $\kappa$ removed. Case A(iii) on the page writes $\underline v^B$, meaning $\underline v_1^B$.
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 16–17, Proposition 2; constants pp. 49–51

import Mathlib
import Definitions.Def_GDPRDataMarkets_Benchmark_Model

namespace GDPRDataMarkets.Benchmark
theorem proposition_2 (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    (P.c ≤ T1 P →
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P1B P ∧ σ.p2 σ.p1 = p2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (vbar1B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (vlow1B P ≤ v → v < vbar1B P →
            σ.buy σ.p1 v = false ∧ σ.p2 σ.p1 + P.c ≤ v) ∧
          (v < vlow1B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c)) ∧
    (T1 P < P.c → P.c < T2 P →
      ∃ σ : Profile, IsEquilibrium P σ ∧ σ.p1 = P2B P ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1,
          (v2B P ≤ v →
            σ.buy σ.p1 v = true ∧ σ.r v = (1 + P.mu - P.sigma) * v ∧
            σ.r v ≤ (1 + P.kL) * v ∧ σ.r v ≤ (1 + P.kH) * v) ∧
          (v < v2B P → σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c)) ∧
    (T2 P ≤ P.c →
      ∃ σ : Profile, IsEquilibrium P σ ∧
        ∀ v ∈ Set.Icc (0 : ℝ) 1, σ.buy σ.p1 v = false ∧ v < σ.p2 σ.p1 + P.c) := by sorry
end GDPRDataMarkets.Benchmark
