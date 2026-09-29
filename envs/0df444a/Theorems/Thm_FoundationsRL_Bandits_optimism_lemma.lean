-- Prove2me | Theorems.Thm_FoundationsRL_Bandits_optimism_lemma
-- name    : FoundationsRL.Bandits.optimism_lemma
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:56:32.485394+00:00
-- url     : https://prove2.me/theorems/28a11519-b38e-4960-9e98-6776eddb3e80
-- title:
--   Lemma 7 — Optimism
-- statement:
--   (Lemma 7, p. 28.) Fix a round and suppose $\underline f(\pi) \le f^\star(\pi) \le
--   \bar f(\pi)$ for every decision $\pi \in \Pi$ (a valid confidence interval at this
--   round), where $\pi^\star$ attains $\max_\pi f^\star(\pi)$. Let
--   $\pi_t := \arg\max_{\pi} \bar f(\pi)$ be the **optimistic action**. Then the
--   instantaneous regret of $\pi_t$ is bounded by the confidence width at $\pi_t$:
--
--   $$f^\star(\pi^\star) - f^\star(\pi_t) \;\le\; \bar f(\pi_t) - \underline f(\pi_t).$$
--
--   This is the key structural fact behind every optimism-based bandit algorithm: as
--   long as the confidence interval at the played action is narrow, the instantaneous
--   regret is small, regardless of which action turns out to be optimal.
--
--   **Formalization Note.** Stated for a single, arbitrary round: `fLo`/`fHi` play the
--   role of $\underline f_t$/$\bar f_t$ at a fixed but unspecified $t$, and `pit` is
--   hypothesized (not derived) to maximize `fHi`, matching the argmax in the book. No
--   time index or history is needed at this level of generality.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 28, Lemma 7

import Mathlib

namespace FoundationsRL.Bandits

/-- Lemma 7 (Optimism), Foster–Rakhlin p. 28. Fix a round with confidence bounds
`fLo ≤ fStar ≤ fHi` valid for every decision. Then the optimistic action `pit`
(the maximizer of `fHi`) has instantaneous regret at most the confidence width
at `pit`: `fStar piStar - fStar pit ≤ fHi pit - fLo pit`. -/
theorem optimism_lemma {A : ℕ} (fStar : Fin A → ℝ) (piStar : Fin A)
    (hStar : ∀ a : Fin A, fStar a ≤ fStar piStar)
    (fLo fHi : Fin A → ℝ) (hCI : ∀ a : Fin A, fStar a ∈ Set.Icc (fLo a) (fHi a))
    (pit : Fin A) (hOpt : ∀ a : Fin A, fHi a ≤ fHi pit) :
    fStar piStar - fStar pit ≤ fHi pit - fLo pit := by sorry

end FoundationsRL.Bandits
