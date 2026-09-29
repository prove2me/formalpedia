-- Prove2me | Theorems.Thm_FoundationsRL_GeneralDM_lemma19_tv_hellinger_kl
-- name    : FoundationsRL.GeneralDM.lemma19_tv_hellinger_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T20:23:38.858575+00:00
-- url     : https://prove2.me/theorems/eaa46158-ccc2-4109-8aac-52b988b45dfb
-- title:
--   Lemma 19 — TV-Hellinger-KL sandwich (Eq. 6.6)
-- statement:
--   This theorem formalizes **Lemma 19** (Foster & Rakhlin, *Foundations of Reinforcement
--   Learning and Interactive Decision Making*, arXiv:2312.16730v1, p. 96, Eq. (6.6)): for all
--   discrete probability distributions $P, Q$ over a finite outcome type $Y$,
--   $$
--   D_{TV}^2(P, Q) \le D_H^2(P, Q) \le D_{KL}(P \| Q).
--   $$
--   This is the information-theoretic divergence-comparison inequality that the DEC's lower-bound
--   argument (Proposition 28) rests on, via the chain rule for KL divergence and the
--   data-processing inequality for TV distance.
--
--   **Formalization Note** Because `klDivDiscrete` returns an `ENNReal` (the book's $D_{KL}$ may
--   be $+\infty$) while `totalVariationDiscrete` and `hellingerSq` return reals, both sides of the
--   theorem are cast into `ENNReal` via `ENNReal.ofReal` so the two inequalities can be stated
--   uniformly as a single conjunction.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 96, Lemma 19, Eq. (6.6)

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Divergences

namespace FoundationsRL.GeneralDM

/-- Lemma 19 (Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision
Making*, arXiv:2312.16730v1, p. 96, Eq. (6.6)): for all discrete probability distributions `P`,
`Q` over a finite outcome type `Y`,

`D²_TV(P, Q) ≤ D²_H(P, Q) ≤ D_KL(P ∥ Q)`.

The two inequalities are stated jointly, as in the book. The left-hand side is a real-valued
inequality between two nonnegative reals; the right-hand side compares against `klDivDiscrete`,
whose codomain is `ENNReal` (the book's `D_KL` may be `+∞`), so both sides of the theorem are
cast into `ENNReal` via `ENNReal.ofReal` to state the two inequalities uniformly. -/
theorem lemma19_tv_hellinger_kl {Y : Type*} [Fintype Y] (P Q : Y → ℝ)
    (hP : (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1) (hQ : (∀ y, 0 ≤ Q y) ∧ ∑ y, Q y = 1) :
    ENNReal.ofReal ((totalVariationDiscrete P Q) ^ 2) ≤ ENNReal.ofReal (hellingerSq P Q) ∧
    ENNReal.ofReal (hellingerSq P Q) ≤ klDivDiscrete P Q := by sorry

end FoundationsRL.GeneralDM
