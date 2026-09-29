-- Prove2me | Theorems.Thm_FoundationsRL_Bandits_confidence_width_potential_bound
-- name    : FoundationsRL.Bandits.confidence_width_potential_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-18T04:57:09.026972+00:00
-- url     : https://prove2.me/theorems/c57cc649-f6b1-450a-ae8f-bcdc8e4029d4
-- title:
--   Lemma 8 — Confidence width potential lemma
-- statement:
--   (Lemma 8, p. 28–29.) For any realized sequence of decisions $\pi_1,\dots,\pi_T$
--   over $A$ actions, the sum of reciprocal-square-root pull counts of the played
--   actions is controlled by a quantitative pigeonhole argument:
--
--   $$\sum_{t=1}^T \Bigl(\frac{1}{\sqrt{n_t(\pi_t)}} \wedge 1\Bigr) \;\lesssim\; \sqrt{AT},$$
--
--   where $n_t(\pi_t)$ is the number of times the round-$t$ decision $\pi_t$ was
--   played before round $t$, and the term is read as $1$ when $n_t(\pi_t) = 0$.
--   Combined with Lemma 7 and the UCB confidence radius (Eq. (2.19)), this bounds
--   UCB's cumulative regret (Proposition 5): every round with a wide confidence
--   interval must be a round where some action's pull count just increased, and this
--   can happen only $O(A)$ times before the interval narrows.
--
--   **Formalization Note.** The existential $\exists\, C > 0$ names the implicit
--   constant of the book's $\lesssim$; the proof (Foster–Rakhlin p. 29) establishes
--   $C$ as an absolute constant not depending on $A$, $T$, or the specific decision
--   sequence `pi`.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 28-29, Lemma 8

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount

namespace FoundationsRL.Bandits

/-- Lemma 8 (Confidence width potential lemma), Foster–Rakhlin p. 28–29:
for any realized decision sequence over `A` actions and horizon `T`,
`Σ_{t=1}^T (1/√(n_t(π_t)) ∧ 1) ≲ √(AT)`, where `n_t(π_t) = 0` contributes
the capped value `1` (the `∧ 1` convention). The constant `C` is universal:
fixed once, before the action count `A`, horizon `T`, and decision sequence
`pi` are quantified, matching the book's `≲`. -/
theorem confidence_width_potential_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : ℕ), 0 < A → ∀ (T : ℕ) (pi : ℕ → Fin A),
        ∑ t ∈ Finset.range T,
            (if pullCount pi t (pi t) = 0 then (1 : ℝ)
              else 1 / Real.sqrt (pullCount pi t (pi t)))
          ≤ C * Real.sqrt ((A : ℝ) * T) := by sorry

end FoundationsRL.Bandits
