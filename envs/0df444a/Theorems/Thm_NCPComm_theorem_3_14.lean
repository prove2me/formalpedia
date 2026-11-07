-- Prove2me | Theorems.Thm_NCPComm_theorem_3_14
-- name    : NCPComm.theorem_3_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:23.386306+00:00
-- url     : https://prove2.me/theorems/8ee215dd-7ac5-4ebb-8091-10fe8b3485c9
-- title:
--   Theorem 3.14 — communication complexity of exact gap disjointness
-- statement:
--   Let $N,k_a,k_b,g\in\mathbb N$ satisfy $1\le g\le k_a\le k_b$ and $3k_a+k_b\le N$. The communication complexity of exact $\mathrm{GapDisj}_{N,g,k_a,k_b}$ in the public-coin model, with error at most $\frac13$, is
--   $$
--   \Omega\Big(\frac{k_a}{g}\Big).
--   $$
--
--   This is the form of Razborov's bound that the reduction needs: dense or sparse inputs and a gap $g$ larger than $1$.
--
--   Differences from the source:
--   - reading: "they must output 1 (accept)" (Definition 3.13), with "Alice's decision" on p.10 → only Alice's output must be correct; reason: stronger for a lower bound: a protocol where both are correct is one where Alice is; the page takes Alice's decision on p.10
--   - encoding: Ω(k_a/g) → κ·(k_a/g) ≤ k with κ > 0 absolute, before all parameters; reason: the meaning of Ω, uniform in all parameters
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Theorem 3.14, p.17

import Mathlib
import Definitions.Def_NCPComm_SolvesExactGapDisj

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Theorem 3.14 (Communication complexity of exact gap disjointness), p.17** (Herman, The
Communication Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript
sha256 714c0353…). If `1 ≤ g ≤ k_a ≤ k_b` and `3k_a + k_b ≤ N`, the public-coin communication
complexity of exact `GapDisj_{N,g,k_a,k_b}` with error at most `1/3` is `Ω(k_a/g)`.

**Formalization Note** `Ω` is an absolute `κ > 0` placed before all parameters. -/
theorem theorem_3_14 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N ka kb g : ℕ), 1 ≤ g → g ≤ ka → ka ≤ kb → 3 * ka + kb ≤ N →
      ∀ (P : DistVerif.Simulation.PubProtocol N) (k : ℕ),
        SolvesExactGapDisj P k g ka kb (1 / 3) → κ * ((ka : ℝ) / g) ≤ (k : ℝ) := by sorry

end NCPComm
