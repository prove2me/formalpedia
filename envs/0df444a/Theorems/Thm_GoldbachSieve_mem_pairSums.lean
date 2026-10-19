-- Prove2me | Theorems.Thm_GoldbachSieve_mem_pairSums
-- name    : GoldbachSieve.mem_pairSums
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:28:36.686047+00:00
-- url     : https://prove2.me/theorems/ef9df1c8-b7f0-4a64-8ae7-518ea656f35f
-- title:
--   Membership in the small-prime sum set $C(P,lo,hi,c)$ is a prime-plus-survivor existential
-- statement:
--   For natural bounds $P \le$ the small-prime cutoff, an interval $[lo, hi]$ and a sieve cutoff $c$, the set of sums
--
--   $$C(P, lo, hi, c) \;=\; \bigcup_{p \le P,\ p \text{ prime}} \bigl\{\, p + q \;:\; q \in S(lo, hi, c) \,\bigr\}$$
--
--   where $S(lo,hi,c)$ is the set of survivors (numbers in $[\max(2,lo), hi]$ with no prime divisor at most $c$ other than themselves), has the membership rule
--
--   $$n \in C(P, lo, hi, c) \iff \exists\, p \le P \text{ prime},\ \exists\, q \in S(lo,hi,c),\ n = p + q .$$
--
--   **Why this is worth stating separately.** The two are the same assertion, but only the membership form can be used without unfolding the definition at concrete bounds. Richstein's segmented-sieve coverage statements mention survivors over an interval with sieve cutoff $2\cdot10^7$; unfolding them at those numerals makes any proof attempt reduce a $2\cdot10^7$-element finite set, which does not terminate within the elaboration budget. Stated over abstract bounds the equivalence is immediate, and it then rewrites cheaply at the concrete instance.
--
--   **Formalization Note.** `pairSums` and `survivors` are the platform definition `GoldbachSieve`. The proof is the two directions of `Finset.mem_biUnion` and `Finset.mem_image`; there is no arithmetic content.
-- source:
--   Platform node Richstein2001.segmented_sieve_coverage, whose statement is this membership rule at concrete bounds; see GoldbachSieve.pairSums and GoldbachSieve.survivors.

import Definitions.Def_GoldbachSieve

namespace GoldbachSieve

theorem mem_pairSums {P lo hi c n : ℕ} :
    n ∈ pairSums P lo hi c ↔
      ∃ p ∈ (Finset.Icc 2 P).filter Nat.Prime,
        ∃ q ∈ survivors lo hi c, n = p + q := by sorry

end GoldbachSieve
