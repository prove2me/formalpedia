-- Prove2me | Theorems.Thm_FoundationsRL_Bandits_ucb_regret_bound
-- name    : FoundationsRL.Bandits.ucb_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:58:15.291829+00:00
-- url     : https://prove2.me/theorems/38b55b4a-9f5d-482f-a344-ae611b68bef1
-- title:
--   Proposition 5 — UCB regret (goal)
-- statement:
--   (Proposition 5, p. 28 — GOAL.) Assume $f^\star(\pi) \in [0,1]$ for every
--   $\pi \in \Pi$, and fix a horizon $T$ and failure probability $\delta \in (0,1)$.
--   The UCB algorithm follows the book's rule: at each round $t$, if some action has
--   never been sampled it plays one such action (the book's confidence radius is
--   $+\infty$ there, so any unsampled action is trivially "most optimistic"); once
--   every action has been sampled at least once, it plays the optimistic action
--   $\pi_t := \arg\max_\pi \bigl(\hat f_t(\pi) + \mathrm{rad}_{T,A,\delta}(n_t(\pi))\bigr)$
--   using the confidence radius of Eq. (2.19). Conditional on the event of Eq. (2.18)
--   — that with probability at least $1-\delta$ the empirical mean concentrates
--   around $f^\star$ within this same radius, at every round $t \le T$ and every
--   *sampled* decision $\pi$ (the event is vacuous, per the book, at $n_t(\pi) = 0$)
--   — UCB's regret satisfies
--
--   $$\mathrm{Reg} \;\lesssim\; \sqrt{AT\log(AT/\delta)}.$$
--
--   This is the chapter's central result: UCB attains the minimax-optimal
--   $\sqrt{AT}$ rate (up to the $\log(AT/\delta)$ factor), a quadratic improvement in
--   $T$ over ε-Greedy's $T^{2/3}$ rate (Proposition 4), by adaptively narrowing
--   exploration to actions whose confidence intervals remain wide, rather than
--   exploring uniformly.
--
--   **Formalization Note.** As with Proposition 4, the "probability at least
--   $1-\delta$" clause is formalized as the deterministic consequence of the
--   concentration event of Eq. (2.18) holding, following the book's own proof
--   ("Let us condition on the event in (2.18) ... Whenever this occurs, we have that
--   $f^\star(\pi) \in [\underline f_t(\pi), \bar f_t(\pi)]$ ... so the confidence
--   intervals are valid."); this event (an application of Hoeffding's inequality for
--   adaptive stopping times, Lemma 33) lies in the book's technical appendix, outside
--   this chapter. The UCB decision rule is stated in the book's own two clauses, not
--   collapsed into a single "maximize the upper confidence bound" rule: an unsampled
--   action's confidence radius is $+\infty$ by Eq. (2.19), so the book always plays
--   an unsampled action first, and only compares finite upper confidence bounds once
--   every action has been sampled at least once. Correspondingly, Eq. (2.18) is only
--   assumed at sampled actions ($n_t(\pi) \neq 0$), since the book's own bound is
--   vacuous (an inequality against $+\infty$) otherwise. The proof route the book
--   takes — Lemma 7 (optimism) + Lemma 8 (potential) + the radius of Eq. (2.19) — is
--   available as the two milestone lemmas `optimism_lemma` and
--   `confidence_width_potential_bound` in this same mission.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 28, Proposition 5

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_FoundationsRL_Bandits_confidenceRadius

namespace FoundationsRL.Bandits

/-- Proposition 5 (UCB regret, GOAL), Foster–Rakhlin p. 28. Assume `fStar π ∈ [0,1]`
for every decision `π`. Suppose `pi` is a realized UCB decision sequence following
the book's rule: at every round `t`, if some action is still unsampled then `pi t`
is one such unsampled action; once every action has been sampled at least once,
`pi t` maximizes the upper confidence bound `fhat t a + confidenceRadius` of
Eq. (2.19) among all actions `a`. Conditional on the event of Eq. (2.18) — that
this holds with probability at least `1 - δ`, restricted to rounds/actions where
the radius is meaningful (`n_t(π) ≠ 0`) since (2.18) is otherwise vacuous — the
UCB algorithm's regret satisfies `Reg ≲ √(AT log(AT/δ))`. The constant `C` is
universal: fixed once, before every instance parameter, matching the book's `≲`. -/
theorem ucb_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (pi : ℕ → Fin A) (fhat : ℕ → Fin A → ℝ),
          -- if some action is still unsampled, UCB plays an unsampled action
          -- (its upper confidence bound is `+∞` in the book).
          (∀ t : ℕ, (∃ a : Fin A, pullCount pi t a = 0) → pullCount pi t (pi t) = 0) →
          -- once every action has been sampled, `pi t` maximizes the upper confidence bound.
          (∀ t : ℕ, (∀ a : Fin A, pullCount pi t a ≠ 0) → ∀ a : Fin A,
              fhat t a + confidenceRadius T A δ (pullCount pi t a) ≤
                fhat t (pi t) + confidenceRadius T A δ (pullCount pi t (pi t))) →
          -- Eq. (2.18): the good event, holding with probability at least `1 - δ`,
          -- restricted to sampled actions (vacuous otherwise in the book).
          (∀ t ∈ Finset.range T, ∀ a : Fin A, pullCount pi t a ≠ 0 →
              |fhat t a - fStar a| ≤ confidenceRadius T A δ (pullCount pi t a)) →
          regret fStar piStar T (fun t a => if a = pi t then (1 : ℝ) else 0) ≤
            C * Real.sqrt ((A : ℝ) * T * Real.log ((A : ℝ) * T / δ)) := by sorry

end FoundationsRL.Bandits
