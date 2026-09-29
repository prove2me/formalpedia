-- Prove2me | Theorems.Thm_OnlineConvexOpt_ChangingEnv_fixed_share_regret
-- name    : OnlineConvexOpt.ChangingEnv.fixed_share_regret
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-19T17:32:51.366707+00:00
-- url     : https://prove2.me/theorems/0ac22064-57d1-43a5-8287-1c690c1aa289
-- title:
--   Theorem 10.3 — Fixed-Share tracking regret
-- statement:
--   **Statement (Theorem 10.3, p. 174, PDF p. 196).** Given a sequence of `α`-exp-concave loss
--   functions, the Fixed-Share algorithm with $\delta = 1/(2T)$ guarantees, for every interval
--   $[r,s]\subseteq[T]$, $\sup_I\{\sum_{t=r}^s f_t(x_t) - \min_{i^\star}\sum_{t=r}^s
--   f_t(x^{i^\star}_t)\} = O(\frac1\alpha\log(NT))$.
--
--   This is a crucial component of the adaptive algorithms the chapter builds next: it says the
--   Fixed-Share mixture never falls far behind whichever expert was locally best on *any*
--   sub-interval, not just the whole horizon.
--
--   **Formalization Note.** The headline display's `O(·)` is replaced by the proof's own
--   explicit derivation, $\sup_I\{\dots\} \le \frac1\alpha\log(2NT) + \frac1\alpha$ (from
--   $\hat p^i_r \ge \delta/N$, $\delta<1/2$, and the specific choice $\delta=1/(2T)$, p. 175) —
--   per `CAPTAIN_BRIEF.md` rule 7 and `BRIEF.md`'s explicit instruction to use the constant
--   chain when the proof pins it down. Stated per-interval (`∀ r s`) rather than as a bundled
--   supremum, since the supremum's nonvacuousness (a finite index set) is then immediate from
--   the per-interval bound holding uniformly.
-- source:
--   Hazan, Introduction to Online Convex Optimization, 2nd ed., arXiv:1909.05207v3, p. 174, Theorem 10.3 (PDF p. 196)

import Mathlib
import Definitions.Def_OnlineConvexOpt_ChangingEnv_FixedShare
import Definitions.Def_OnlineConvexOpt_ChangingEnv_ExpConcave

namespace OnlineConvexOpt.ChangingEnv

/-- Theorem 10.3 (Hazan, *Introduction to Online Convex Optimization*, 2nd ed.,
arXiv:1909.05207v3, p. 174, PDF p. 196). Given a sequence of `α`-exp-concave loss functions,
the Fixed-Share algorithm with `δ = 1/(2T)` guarantees, for every interval `[r,s] ⊆ [0,T-1]`
and every expert `i`,
`∑_{t=r}^s f_t(x_t) - ∑_{t=r}^s f_t(x^i_t) ≤ (1/α)log(2NT) + 1/α`.

The book's headline display states this as a bare `O((1/α)log(NT))`; the explicit constant
`(1/α)log(2NT) + 1/α` is what the proof on p. 175 (PDF p. 197) actually derives (using
`p^i_r ≥ δ/N`, `δ < 1/2` and the specific choice `δ = 1/(2T)`), and is drafted here per
`CAPTAIN_BRIEF.md` rule 7/`BRIEF.md`'s explicit instruction to use it when available. -/
theorem fixed_share_regret
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {N : ℕ} (hN : 0 < N)
    (α : ℝ) (hαpos : 0 < α)
    (f : ℕ → E → ℝ) (hfexp : ∀ t, IsAlphaExpConcaveOn Set.univ (f t) α)
    (T : ℕ) (hT : 1 ≤ T)
    (δ : ℝ) (hδ : δ = 1 / (2 * T))
    (xi : ℕ → Fin N → E) (p phat : ℕ → Fin N → ℝ) (x : ℕ → E)
    (hrun : IsFixedShareRun f α δ xi p phat x)
    (r s : ℕ) (hrs : r ≤ s) (hsT : s < T) (i : Fin N) :
    (∑ t ∈ Finset.Icc r s, f t (x t)) - ∑ t ∈ Finset.Icc r s, f t (xi t i) ≤
      (1 / α) * Real.log (2 * N * T) + 1 / α := by sorry

end OnlineConvexOpt.ChangingEnv
