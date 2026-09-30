-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_flexibility_premium_nonneg
-- name    : MixFlex.RiskNeutral.flexibility_premium_nonneg
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:58:46.253983+00:00
-- url     : https://prove2.me/theorems/91f42b3b-4059-4887-9bcf-9fd88ad1813a
-- title:
--   PROPOSITION 1 — the risk-neutral flexibility premium is nonnegative, and zero at low reliability or perfect correlation
-- statement:
--   Consider the SD and SF networks of the mission's model: $N$ products with common margin $p>0$, dedicated resources with marginal total cost $c>0$, a flexible resource with marginal total cost $c_{N+1}$, common reliability $\theta\in[0,1]$ and committed cost fraction $\lambda\in[0,1]$, Bernoulli yields independent of each other and of the nonnegative integrable demand vector $\tilde X$. For a risk-neutral firm and **any** such demand vector:
--
--   1. the flexibility premium is nonnegative, $\Delta_{RN}\ge 0$, for all $0\le\theta\le 1$: SF is weakly preferred to SD whenever $c_{N+1}\le c$;
--   2. if
--   $$
--   0\le\theta\le\frac{\lambda c}{p-(1-\lambda)c},
--   $$
--   then $\Delta_{RN}=0$: at $c_{N+1}=c$ the firm is indifferent, $V^{SF,*}_{RN}=V^{SD,*}_{RN}$;
--   3. if $\rho_X=\mathbf 1$, i.e. every pair of demands has correlation coefficient $1$, then $\Delta_{RN}=0$.
--
--   This is Proposition 1 of Tomlin and Wang (2005). It says that under risk neutrality, with equal reliabilities and costs, the demand-pooling benefit of a flexible resource always outweighs its resource-aggregation risk, and that even without a pooling benefit (perfectly correlated demand) the firm is still indifferent.
--
--   **Formalization Note** $\Delta_{RN}$ is not defined as a number, because Definition 1's indifference cost need not exist or be unique (in regime 2 both optimal values are $0$ for every $c_{N+1}$ near $c$). "$\Delta\ge 0$" is encoded as "SF is weakly preferred for every $c_{N+1}\le c$", following the page's "the firm prefers the SF network as long as $c_{N+1}\le(1+\Delta)c$"; "$\Delta=0$" as "SF and SD are each weakly preferred to the other at $c_{N+1}=c$". Weak preference $V^{SF,*}\ge V^{SD,*}$ is "every nonnegative SD investment is matched by a nonnegative SF investment", avoiding real suprema. No joint density is assumed: the proposition is for any demand vector, and a density would make part 3 vacuous for $N\ge 2$. Part 3 adds square integrability and positive variances, the conditions under which correlation coefficients exist. When $p\le(1-\lambda)c$, Lean's value of $\lambda c/(p-(1-\lambda)c)$ is $\le 0$ (it is $0$ on division by zero), so part 2 then applies only at $\theta=0$, where it is true.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 42, §3.1, PROPOSITION 1; DEFINITIONS 1–2, p. 41

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- Proposition 1, p. 42. For any demand random vector: (i) the risk-neutral flexibility premium is
nonnegative for all `0 ≤ θ ≤ 1` (SF is preferred whenever `c_{N+1} ≤ c`); (ii)
`θ ≤ λc/(p − (1 − λ)c)` implies `Δ_RN = 0` (`c_{N+1} = c` is an indifference cost); (iii) if all
pairwise demand correlations equal `1`, then `Δ_RN = 0`. -/
theorem flexibility_premium_nonneg (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) :
    PremiumNonneg P μ X Y ∧
    (P.theta ≤ P.lam * P.c / (P.p - (1 - P.lam) * P.c) → PremiumZero P μ X Y) ∧
    ((∀ n, MemLp (fun ω => X ω n) 2 μ) → (∀ n, 0 < variance (fun ω => X ω n) μ) →
      (∀ m n, correlation μ (fun ω => X ω m) (fun ω => X ω n) = 1) → PremiumZero P μ X Y) := by sorry

end MixFlex.RiskNeutral
