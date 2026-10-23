-- Prove2me | Theorems.Thm_KellerTrotter2017_thm16_8_erdos_ko_rado_faithful
-- name    : KellerTrotter2017.thm16_8_erdos_ko_rado_faithful
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-23T01:26:52.033431+00:00
-- url     : https://prove2.me/theorems/a719ac7a-f7c4-4284-9a96-e8f0cf08ff0e
-- title:
--   Theorem 16.8 (Erdős–Ko–Rado) — the maximum intersecting family of $k$-sets has size $\binom{n-1}{k-1}$
-- statement:
--   Let $n$ and $k$ be positive integers with $n \ge 2k$. Consider families $\mathcal F$ of subsets of $[n] = \{1, \dots, n\}$ such that
--
--   1. $A \cap B \ne \emptyset$ for all $A, B \in \mathcal F$, and
--   2. $|A| = k$ for all $A \in \mathcal F$.
--
--   Then the maximum size of such a family is
--
--   $$\max |\mathcal F| = \binom{n-1}{k-1}.$$
--
--   This is Theorem 16.8 (Erdős–Ko–Rado) of Keller and Trotter, *Applied Combinatorics*, Section 16.2 (extremal set theory): the bound is attained by all $k$-sets containing a fixed element.
--
--   **Formalization Note** $[n]$ is represented by `Fin n`; "maximum size" is `IsGreatest` of the set of attainable sizes, so both the upper bound and its attainment are asserted. $n \ge 2k \ge 2$ makes $n - 1$ and $k - 1$ exact.
-- source:
--   Keller & Trotter, Applied Combinatorics (2017 Edition), p. 319, Theorem 16.8

import Mathlib

theorem KellerTrotter2017.thm16_8_erdos_ko_rado_faithful (n k : ℕ) (hk : 0 < k) (hn : 2 * k ≤ n) :
    IsGreatest {m : ℕ | ∃ 𝒜 : Finset (Finset (Fin n)),
        (∀ A ∈ 𝒜, A.card = k) ∧ (∀ A ∈ 𝒜, ∀ B ∈ 𝒜, (A ∩ B).Nonempty) ∧ 𝒜.card = m}
      ((n - 1).choose (k - 1)) := by sorry
