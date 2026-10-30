-- Prove2me | Theorems.Thm_MonopolyDemandUncertainty_SBSMP_proposition_1_condition_4ii
-- name    : MonopolyDemandUncertainty.SBSMP.proposition_1_condition_4ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:11:22.471903+00:00
-- url     : https://prove2.me/theorems/a868b5cf-0cea-4036-bbac-f653f858b770
-- title:
--   Proposition 1 (SBSMP), Condition 4(ii) branch, p. 5 (PDF 6) — state-by-state monopoly pricing is an optimal deterministic BIC and EIR mechanism
-- statement:
--   Consider a zero-cost monopolist facing a continuum of unit-demand consumers with valuations in $V = [\underline v, \bar v]$, $0 \le \underline v < \bar v$. The demand state is low (state 1) with probability $\alpha_1 \in (0,1)$ and high (state 2) with probability $\alpha_2 = 1 - \alpha_1$; $D_i(v)$ is the mass of consumers with valuation above $v$ in state $i$, so $D_i(\bar v) = 0$. Assume
--
--   1. Condition 1: each $D_i$ is $C^2$ with $D_i' < 0$ on $V$;
--   2. Condition 2: $Z(v) = (-D_1'(v))/(-D_2'(v))$ satisfies $Z'(v) < 0$ on $V$;
--   3. Condition 3: $D_i'' < 0$ on $V$;
--   4. Condition 4(ii): $\frac{\alpha_1}{\alpha_2} Z(v) > 1$ for all $v \in V$.
--
--   Let $p_i^m$ be a monopoly price in state $i$, i.e. a maximizer of $p\,D_i(p)$ over $V$. Then state-by-state monopoly pricing (SBSMP), which sells in state $i$ to every $v \ge p_i^m$ at price $p_i^m$, is Bayesian incentive compatible and ex post individually rational, and for every deterministic BIC and EIR mechanism $(x,t)$,
--   $$\pi(x,t) \le \pi_{\mathrm{SBSMP}} = \alpha_1 D_1(p_1^m)\,p_1^m + \alpha_2 D_2(p_2^m)\,p_2^m .$$
--
--   The result says that a monopolist who learns the aggregate state from consumers' reports cannot do better, under Bayesian rather than ex post incentive compatibility, than posting the monopoly price of each state.
--
--   **Formalization Note** The page assumes "Conditions 1–4", where Condition 4 is the disjunction of 4(i) $\frac{\alpha_1}{\alpha_2}Z<1$ on $V$ and 4(ii). Only the 4(ii) branch is posed: under 4(i) the proposition is false. With $V=[1/5,1]$, $D_1 = 1-v^2$, $D_2 = 1-v^3$ and $\alpha_1 = 1/10$ (Conditions 1–3 and 4(i) hold), the mechanism that sells only in state 2 at price $409/675$ to $[409/675, 17/25)$ and in both states at prices $0$ and $17/25$ to $[17/25,1]$ is BIC and EIR and earns $\approx 0.46972$, more than SBSMP's $\approx 0.46371$. "The optimal mechanism is SBSMP" is posed as "SBSMP is BIC, EIR and profit-maximal"; uniqueness is not claimed. The hypotheses $D_i(\bar v)=0$, $0\le\underline v$ and $0<\alpha_1<1$ are added and make the page's model explicit. The profit is a Lebesgue integral and is $0$ for a mechanism whose integrand is not integrable; since SBSMP's profit is nonnegative, such mechanisms satisfy the bound trivially. No integrability or measurability is assumed on the competing mechanism. The printed proof of this branch is incomplete (the bound (A.46) in Claim 5 is not an upper bound).
-- source:
--   Peck, Rampal, Optimal Monopoly Mechanisms with Demand Uncertainty, Mathematics of Operations Research (2021), Articles in Advance, doi:10.1287/moor.2020.1120, p. 5, Proposition 1, (6), Condition 4(ii)

import Mathlib
import Definitions.Def_MonopolyDemandUncertainty_SBSMP_Setting

namespace MonopolyDemandUncertainty.SBSMP

open MeasureTheory Set

/-- Proposition 1 (SBSMP), p. 5 (PDF 6), Condition 4(ii) branch: under Conditions 1, 2, 3 and
4(ii), state-by-state monopoly pricing at monopoly prices `p₁, p₂` (maximizers of `p D_i(p)` on
`V`) is BIC and EIR, and its profit is at least that of every deterministic BIC and EIR
mechanism. (The printed Condition 4 also allows branch 4(i), under which the claim is false.) -/
theorem proposition_1_condition_4ii (E : Economy) (hE : E.Valid)
    (h1 : E.Condition1) (h2 : E.Condition2) (h3 : E.Condition3) (h4 : E.Condition4ii)
    (p₁ p₂ : ℝ) (hp₁ : E.IsMonopolyPrice 0 p₁) (hp₂ : E.IsMonopolyPrice 1 p₂) :
    E.IsBIC (sbsmp p₁ p₂) ∧ E.IsEIR (sbsmp p₁ p₂) ∧
      ∀ M : Mechanism, E.IsBIC M → E.IsEIR M → E.profit M ≤ E.profit (sbsmp p₁ p₂) := by sorry
end MonopolyDemandUncertainty.SBSMP
