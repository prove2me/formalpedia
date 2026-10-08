-- Prove2me | Theorems.Thm_OnlineConvexOpt_ChangingEnv_simple_flh_adaptive_regret_v2
-- name    : OnlineConvexOpt.ChangingEnv.simple_flh_adaptive_regret_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:21:42.193488+00:00
-- url     : https://prove2.me/theorems/cb6a49ca-70f1-43c3-a224-4e61efb4fa17
-- title:
--   Theorem 10.6 — Adaptive regret of Simple-FLH (genuine interval maximum, exp-concavity on $K$)
-- statement:
--   **Statement (Theorem 10.6).** Let $K$ be a nonempty convex decision set, $\alpha>0$, and $f_0,f_1,\dots$ cost functions that are $\alpha$-exp-concave on $K$ and bounded below on $K$. Run Simple-FLH (Algorithm 32) for $T\ge1$ rounds: Fixed Share (Algorithm 30) with $N=T$ experts and $\delta=1/(2T)$, where expert $i$ predicts points $x^i_t\in K$ such that, on every interval $[r,s]\subseteq[0,T-1]$ with $i\le r$, its interval regret $\sum_{t=r}^{s}f_t(x^i_t)-\min_{y\in K}\sum_{t=r}^{s}f_t(y)$ is at most $\mathrm{Regret}_T(A)$ (expert $i$ is a fresh copy of the OCO algorithm $A$ started at round $i$). Then
--   $$\mathrm{AdaptiveRegret}_T(\text{Simple-FLH})\le\mathrm{Regret}_T(A)+\frac1\alpha\log(2T^2)+\frac1\alpha,$$
--   the explicit form of the book's $\mathrm{Regret}_T(A)+O(\frac1\alpha\log T)$, where the adaptive regret is the maximum interval regret over all contiguous $[r,s]\subseteq[0,T-1]$ (Definition 10.2).
--
--   **Formalization Note.** The retired version used `AdaptiveRegretT`/`IntervalRegret` of `OnlineConvexOpt_ChangingEnv_Regret`, whose nested `⨆`/`⨅` binders evaluate on $\mathbb R$ to junk $0$ outside their index sets (forcing the adaptive regret to be $\ge0$ and the comparator to be $0$ for empty $K$), had no nonemptiness of $K$, and assumed exp-concavity on all of $E$ — a hypothesis only constant costs satisfy, since a positive concave function on a whole normed space is constant. The new statement imports `OnlineConvexOpt_ChangingEnv_Regret_v2`, where the interval regret subtracts the real infimum of the interval cost over $K$ and the adaptive regret is the real supremum of the finite nonempty set of interval regrets; it assumes $K$ nonempty and convex, exp-concavity on $K$, costs bounded below on $K$ (the OCO standing boundedness convention, which makes every interval infimum genuine), and expert predictions in $K$ (the book's placeholder $x^i_t=0$ for not-yet-started experts is read as an arbitrary point of $K$, so that the fixed-share mixture stays in $K$, where exp-concavity is available). The expert hypothesis is stated with the same `IntervalRegret`. The constant $\frac1\alpha\log(2T^2)+\frac1\alpha$ is Theorem 10.3's bound with $N=T$, $\delta=1/(2T)$.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 177, Theorem 10.6 (PDF p. 199)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret_v2
import Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
import Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave

namespace OnlineConvexOpt.ChangingEnv

/-- Theorem 10.6 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 177, PDF p. 199). Algorithm 32 (Simple-FLH) guarantees
`AdaptiveRegret_T(Simple-FLH) ≤ Regret_T(A) + O((1/α)log T)`.

Simple-FLH (p. 176) runs Fixed-Share (Algorithm 30) with `N = T` experts, `δ = 1/(2T)`, where
expert `i`'s decisions are those of a fresh copy of the OCO algorithm `A` started at round `i`
(`xi t i ∈ K` for every round and expert; the book's placeholder `x^i_t = 0` for not-yet-started
experts is read as an arbitrary point of the decision set `K`, so that every played mixture
stays in `K`). `RegretBoundA` stands for `Regret_T(A)`, an abstract bound on `A`'s own
(non-adaptive) regret, supplied via `hxi`: for every expert `i` and every sub-interval `[r,s]` it
is active on (`i ≤ r`), its interval regret against the best fixed point of `K` is at most
`RegretBoundA` — the book's own reduction step "`∑_{t∈I} f_t(x^r_t) = Regret_{s-r+1}(A) ≤
Regret_T(A)`" (p. 177). The explicit constant `(1/α)log(2T²) + 1/α` (from `N = T` in Theorem
10.3's bound) is drafted in place of the headline's `O((1/α)log T)`.

Corrected version: `AdaptiveRegretT`/`IntervalRegret` are the `OnlineConvexOpt_ChangingEnv_Regret_v2`
versions (genuine maximum over the intervals and genuine infimum over `K`; the retired binders
returned junk `0` values outside the index sets), `K` is a nonempty convex set, the costs are
`α`-exp-concave on `K` (the retired hypothesis "exp-concave on all of `E`" is satisfiable only by
constant costs, since a positive concave function on a whole normed space is constant) and
bounded below on `K` (the OCO standing boundedness assumption, which makes every interval
infimum genuine). -/
theorem simple_flh_adaptive_regret_v2
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (hKconv : Convex ℝ K) (hKne : K.Nonempty) (α : ℝ) (hαpos : 0 < α)
    (f : ℕ → E → ℝ) (hfexp : ∀ t, IsAlphaExpConcaveOn K (f t) α)
    (hfbdd : ∀ t, BddBelow (f t '' K))
    (RegretBoundA : ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (xi : ℕ → Fin T → E) (hxiK : ∀ t i, xi t i ∈ K)
    (hxi : ∀ (i : Fin T) (r s : ℕ), (i : ℕ) ≤ r → r ≤ s → s < T →
      IntervalRegret K f (fun t => xi t i) r s ≤ RegretBoundA)
    (p phat : ℕ → Fin T → ℝ) (x : ℕ → E)
    (hrun : IsFixedShareRun f α (1 / (2 * (T : ℝ))) xi p phat x) :
    AdaptiveRegretT K f x T ≤
      RegretBoundA + (1 / α) * Real.log (2 * (T : ℝ) ^ 2) + 1 / α := by sorry

end OnlineConvexOpt.ChangingEnv
