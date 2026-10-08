-- Prove2me | Theorems.Thm_ObliviousRAM_LowerBound_theorem_6_1
-- name    : ObliviousRAM.LowerBound.theorem_6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:10:40.720979+00:00
-- url     : https://prove2.me/theorems/a519ede4-a4e7-460b-a3dc-5932b5ae6d76
-- title:
--   THEOREM 6.1, p. 469 — m and Ω(t log t) access lower bounds
-- statement:
--   In the ball-and-cell game used to prove Theorem 6.1, let a correct oblivious randomized player have hand capacity $b$, $m$ initially occupied cells, and $t$ request rounds. Every positive-probability run $a$ uses at least $m$ accesses when $t\ge1$. Moreover, for each fixed $b$ there are $c_b>0$ and a threshold $T_b$ such that, for every $t\ge T_b$ with $m=t$, every such player and every positive-probability run satisfy
--
--   $$
--   |a|\ge m,\qquad |a|\ge c_b\,t\log t\quad(m=t\text{ in the second inequality}).
--   $$
--
--   This is the paper's $\max\{m,\Omega(t\log t)\}$ access requirement, stated for the game in the proof; in it $m$ represents the theorem's $|y|$ initially occupied memory words.
--
--   **Formalization Note** The RAM machine model of §2 is replaced by the proof's more permissive ball-and-cell game. The constant and threshold depend only on the fixed hand size $b$, never on $t$ or the player. `Real.log` is the natural logarithm, whose base affects only $c_b$. Each positive-probability run is bounded, rather than only an expected run length. The printed counting display in the proof is false for repeated round-end indices; the corrected milestones retain the theorem's asymptotic conclusion.
-- source:
--   Goldreich and Ostrovsky, Software protection and simulation on oblivious RAMs, J. ACM 43 (1996), p. 469, THEOREM 6.1 (proof pp. 469–470); https://doi.org/10.1145/233551.233553

import Mathlib
import Definitions.Def_ObliviousRAM_LowerBound_Game

namespace ObliviousRAM.LowerBound

theorem theorem_6_1 :
    (∀ (b m t : ℕ), 1 ≤ t → ∀ P : ObliviousPlayer b m t, ∀ r, ∀ a ∈ (P.play r).support,
      m ≤ a.length) ∧
    (∀ b : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ T : ℕ, ∀ t : ℕ, T ≤ t →
      ∀ P : ObliviousPlayer b t t, ∀ r, ∀ a ∈ (P.play r).support,
        c * (t : ℝ) * Real.log t ≤ (a.length : ℝ)) := by sorry

end ObliviousRAM.LowerBound
