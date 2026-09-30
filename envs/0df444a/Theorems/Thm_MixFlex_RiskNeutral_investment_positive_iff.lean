-- Prove2me | Theorems.Thm_MixFlex_RiskNeutral_investment_positive_iff
-- name    : MixFlex.RiskNeutral.investment_positive_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:57:01.712438+00:00
-- url     : https://prove2.me/theorems/2e907872-acf1-4d84-adee-eebde330a9f1
-- title:
--   Proof of PROPOSITION 1(ii) — investment is worthwhile iff θ > λc/(p − (1 − λ)c)
-- statement:
--   In the mission's model at $c_{N+1}=c$:
--
--   1. If $\theta\le \lambda c/(p-(1-\lambda)c)$, then every nonnegative SF investment and every nonnegative SD investment has nonpositive expected profit; hence investing nothing is optimal in both networks and $V^{SF,*}_{RN}=V^{SD,*}_{RN}=0$.
--   2. If $\theta> \lambda c/(p-(1-\lambda)c)$ with $p>(1-\lambda)c$, there is at least one product ($N\ge 1$), and every demand is almost surely positive, then some flexible level $K_{N+1}>0$ has $V^{SF}_{RN}(K_{N+1})>0$, and for every product $n$ some dedicated level $K_n>0$ (with nothing invested in the other dedicated resources) has positive expected SD profit.
--
--   In the paper's words, the flexible-only and dedicated-only resource levels are positive if and only if
--   $$
--   \theta>\frac{\lambda c}{p-(1-\lambda)c},
--   $$
--   and therefore $\theta\le\lambda c/(p-(1-\lambda)c)$ implies $V^{SF,*}_{RN}-V^{SD,*}_{RN}=0$.
--
--   **Formalization Note** "The optimal level is positive" is rendered as "some positive level earns positive expected profit", and its negation as "no nonnegative level earns positive expected profit". Part 2 assumes $p>(1-\lambda)c$ (so the threshold is a genuine ratio), $N\ge 1$, and almost surely positive demand; the last replaces the paper's density assumption, without which "only if" fails (demand that is zero with positive probability can make every small investment unprofitable). When $p\le(1-\lambda)c$, Lean's value of the threshold is $\le 0$ and part 1 applies only at $\theta=0$.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 52, Appendix A, proof of PROPOSITION 1(ii)

import Mathlib
import Definitions.Def_MixFlex_RiskNeutral_Model

namespace MixFlex.RiskNeutral

open MeasureTheory ProbabilityTheory

/-- Proof of Proposition 1(ii), p. 52: at `c_{N+1} = c`, (a) if `θ ≤ λc/(p − (1 − λ)c)` then no
nonnegative SF or SD investment has positive expected profit (so zero investment is optimal in both
networks); (b) if `θ > λc/(p − (1 − λ)c)` with `p > (1 − λ)c`, and demands are almost surely
positive, then a positive flexible level and, for each product, a positive dedicated level earn
positive expected profit. -/
theorem investment_positive_iff (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (Y : Ω → Fin (N + 1) → ℝ)
    (hS : Setting P μ X Y) :
    (P.theta ≤ P.lam * P.c / (P.p - (1 - P.lam) * P.c) →
      (∀ K : ℝ, 0 ≤ K → vSF P μ X Y P.c K ≤ 0) ∧
      (∀ K : Fin N → ℝ, (∀ n, 0 ≤ K n) → vSD P μ X Y K ≤ 0)) ∧
    (P.lam * P.c / (P.p - (1 - P.lam) * P.c) < P.theta → (1 - P.lam) * P.c < P.p → 0 < N →
      (∀ n, μ.real {ω | 0 < X ω n} = 1) →
      (∃ K : ℝ, 0 < K ∧ 0 < vSF P μ X Y P.c K) ∧
      (∀ n : Fin N, ∃ Kn : ℝ, 0 < Kn ∧ 0 < vSD P μ X Y (Pi.single n Kn))) := by sorry

end MixFlex.RiskNeutral
