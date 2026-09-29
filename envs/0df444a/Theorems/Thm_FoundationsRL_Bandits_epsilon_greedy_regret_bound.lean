-- Prove2me | Theorems.Thm_FoundationsRL_Bandits_epsilon_greedy_regret_bound
-- name    : FoundationsRL.Bandits.epsilon_greedy_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:57:35.941464+00:00
-- url     : https://prove2.me/theorems/da7811a4-c7d7-4d24-993d-c98650a9bbe5
-- title:
--   Proposition 4 — ε-Greedy regret
-- statement:
--   (Proposition 4, p. 24.) Assume the mean reward function satisfies
--   $f^\star(\pi) \in [0,1]$ for every $\pi \in \Pi$, and fix a horizon $T$ and
--   failure probability $\delta \in (0,1)$. The ε-Greedy algorithm (Eq. (2.6)) plays,
--   at each round $t$, the empirical maximizer
--   $\hat\pi_t := \arg\max_\pi \hat f_t(\pi)$ with probability $1-\varepsilon$ and a
--   uniformly random decision with probability $\varepsilon$, for $\varepsilon$ set to
--   the value
--
--   $$\varepsilon = \Bigl(\frac{A\log(AT/\delta)}{T}\Bigr)^{1/3}$$
--
--   that balances the exploration/exploitation trade-off in the proof (Eq. (2.14)).
--   Conditional on the estimation event of Eq. (2.9) — that with probability at least
--   $1-\delta$ the empirical mean is within $\sqrt{A\log(AT/\delta)/(\varepsilon t)}$
--   of $f^\star$ at every round $t \le T$ — the algorithm's regret satisfies
--
--   $$\mathrm{Reg} \;\lesssim\; A^{1/3} T^{2/3} \log^{1/3}(AT/\delta).$$
--
--   This is the chapter's first regret bound and motivates the search for a better
--   exploration strategy: it establishes sublinear regret but at a worse $T^{2/3}$
--   rate than the $\sqrt{T}$-rate UCB (Proposition 5) later attains.
--
--   **Formalization Note.** The "with probability $1-\delta$" clause of the book's
--   proposition is formalized as the deterministic consequence of the estimation
--   event of Eq. (2.9) holding — precisely how the book's own proof proceeds ("we
--   will show that the event $\mathcal{E}_t$ ... occurs ... with probability at least
--   $1-\delta$", then reasons deterministically conditional on it). The underlying
--   high-probability claim (built from Hoeffding's and Bernstein's inequalities,
--   Lemma 33/Lemma 5 of the book's appendix) is outside this chapter and is not itself
--   a milestone here.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 24, Proposition 4

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_regret

namespace FoundationsRL.Bandits

/-- Proposition 4 (ε-Greedy regret), Foster–Rakhlin p. 24. Assume `fStar π ∈ [0,1]`
for every decision `π`. Conditional on the estimation event of Eq. (2.9) — that at
every round `t ≤ T` the empirical mean concentrates around `fStar` at the rate the
ε-fraction of uniform exploration buys — and with `ε` set to the value (Eq. (2.14))
that balances the two terms of the regret decomposition, the ε-Greedy algorithm's
regret satisfies `Reg ≲ A^{1/3} T^{2/3} log^{1/3}(AT/δ)`. The constant `C` is
universal: fixed once, before every instance parameter, matching the book's `≲`. -/
theorem epsilon_greedy_regret_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (fStar : Fin A → ℝ),
        (∀ a : Fin A, fStar a ∈ Set.Icc (0 : ℝ) 1) →
        ∀ (piStar : Fin A), (∀ a : Fin A, fStar a ≤ fStar piStar) →
        ∀ (T : ℕ), 0 < T → ∀ (δ : ℝ), 0 < δ → δ < 1 →
        ∀ (ε : ℝ), ε = ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / T) ^ ((1 : ℝ) / 3) →
        ∀ (piHat : ℕ → Fin A) (p : ℕ → Fin A → ℝ),
          -- Eq. (2.6): ε-Greedy plays the empirical maximizer with probability `1 - ε`
          -- and a uniform random decision with probability `ε`.
          (∀ t : ℕ, ∀ a : Fin A,
              p t a = (1 - ε) * (if a = piHat t then (1 : ℝ) else 0) + ε * (1 / A)) →
          ∀ (fhat : ℕ → Fin A → ℝ),
          (∀ t : ℕ, ∀ a : Fin A, fhat t a ≤ fhat t (piHat t)) →
          -- Eq. (2.9): the good event, holding with probability at least `1 - δ`.
          (∀ t ∈ Finset.range T, ∀ a : Fin A,
              |fhat t a - fStar a| ≤ Real.sqrt ((A : ℝ) * Real.log ((A : ℝ) * T / δ) / (ε * (t + 1)))) →
          regret fStar piStar T p ≤
            C * (A : ℝ) ^ ((1 : ℝ) / 3) * (T : ℝ) ^ ((2 : ℝ) / 3) *
              (Real.log ((A : ℝ) * T / δ)) ^ ((1 : ℝ) / 3) := by sorry

end FoundationsRL.Bandits
