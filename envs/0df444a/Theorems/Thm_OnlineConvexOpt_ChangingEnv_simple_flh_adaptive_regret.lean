-- Prove2me | Theorems.Thm_OnlineConvexOpt_ChangingEnv_simple_flh_adaptive_regret
-- name    : OnlineConvexOpt.ChangingEnv.simple_flh_adaptive_regret
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T17:33:23.059984+00:00
-- url     : https://prove2.me/theorems/862221eb-65fe-4186-93ba-ea6be5c91279
-- title:
--   Theorem 10.6 — Simple-FLH adaptive regret bound (goal)
-- statement:
--   **Statement (Theorem 10.6, p. 177, PDF p. 199).** Algorithm 32 (Simple-FLH) guarantees
--   $\mathrm{AdaptiveRegret}_T(\text{Simple-FLH}) \le \mathrm{Regret}_T(A) +
--   O(\frac1\alpha\log T)$.
--
--   This is the chapter's payoff: an efficient reduction that converts *any* OCO algorithm `A`
--   for `α`-exp-concave losses into an algorithm with low adaptive regret, at only an additive
--   $O(\frac1\alpha\log T)$ cost over `A`'s own ordinary regret — the strongly-adaptive property
--   §10.2.1 asks whether is achievable at all, answered affirmatively here.
--
--   **Formalization Note.** Simple-FLH runs Fixed-Share with `N = T` experts, `δ = 1/(2T)`,
--   where expert `i`'s decisions come from a fresh copy of `A` started at round `i`; the proof's
--   only use of this connection is the regret bound each expert inherits from `A`
--   (`∑_{t∈I} f_t(x^i_t) = Regret_{s-i+1}(A) ≤ Regret_T(A)`), captured here as the hypothesis
--   `hxi` rather than by re-deriving Algorithm 32's exact re-indexing formula for `x^i_t`, which
--   never enters the numerical bound — see `MODERATION_NOTES.md`. The headline `O(1/α·log T)` is
--   replaced by the explicit constant `(1/α)log(2T²) + 1/α` the proof derives (substituting
--   `N=T` into Theorem 10.3's own explicit bound), per the same rule 7/`BRIEF.md` guidance as
--   `fixed_share_regret`.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 177, Theorem 10.6 (PDF p. 199)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_Regret
import Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
import Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave

namespace OnlineConvexOpt.ChangingEnv

/-- Theorem 10.6 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 177, PDF p. 199). Algorithm 32 (Simple-FLH) guarantees
`AdaptiveRegret_T(Simple-FLH) ≤ Regret_T(A) + O((1/α)log T)`.

Simple-FLH (p. 176) runs Fixed-Share (Algorithm 30) with `N = T` experts, `δ = 1/(2T)`, where
expert `i`'s decisions are those of a fresh copy of the OCO algorithm `A` started at round `i`.
`RegretBoundA` stands for `Regret_T(A)`, an abstract bound on `A`'s own (non-adaptive) regret,
supplied here via `hxi`: for every expert `i` and every sub-interval `[r,s]` it is active on
(`i ≤ r`), its cumulative loss against the best fixed point in `K` is within `RegretBoundA` —
the book's own reduction step "`∑_{t∈I} f_t(x^r_t) = Regret_{s-r+1}(A) ≤ Regret_T(A)`" (p. 177),
which is the only property of expert `i`'s connection to `A` the proof actually uses (Algorithm
32's exact re-indexing formula for `x^i_t` does not itself enter the numerical bound) — see
`MODERATION_NOTES.md`. The explicit constant `(1/α)log(2T²) + 1/α` (from `N = T` in Theorem
10.3's bound) is drafted in place of the headline's `O((1/α)log T)`, per the same rule 7/`BRIEF.md`
guidance as `fixed_share_regret`. -/
theorem simple_flh_adaptive_regret
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (α : ℝ) (hαpos : 0 < α)
    (f : ℕ → E → ℝ) (hfexp : ∀ t, IsAlphaExpConcaveOn Set.univ (f t) α)
    (RegretBoundA : ℝ)
    (T : ℕ) (hT : 1 ≤ T)
    (xi : ℕ → Fin T → E)
    (hxi : ∀ (i : Fin T) (r s : ℕ), (i : ℕ) ≤ r → r ≤ s → s < T →
      (∑ t ∈ Finset.Icc r s, f t (xi t i)) - ⨅ y ∈ K, ∑ t ∈ Finset.Icc r s, f t y ≤
        RegretBoundA)
    (p phat : ℕ → Fin T → ℝ) (x : ℕ → E)
    (hrun : IsFixedShareRun f α (1 / (2 * T)) xi p phat x) :
    AdaptiveRegretT K f x T ≤
      RegretBoundA + (1 / α) * Real.log (2 * (T : ℝ) ^ 2) + 1 / α := by sorry

end OnlineConvexOpt.ChangingEnv
