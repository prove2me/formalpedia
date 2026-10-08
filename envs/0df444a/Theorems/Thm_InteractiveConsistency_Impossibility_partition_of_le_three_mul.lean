-- Prove2me | Theorems.Thm_InteractiveConsistency_Impossibility_partition_of_le_three_mul
-- name    : InteractiveConsistency.Impossibility.partition_of_le_three_mul
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:31:11.781787+00:00
-- url     : https://prove2.me/theorems/9464dde9-574c-4f4c-981b-10ff23c54e13
-- title:
--   Section 4, proof (p. 232) — if 3 ≤ n ≤ 3m, P splits into three nonempty parts of size at most m
-- statement:
--   Let $P$ be a finite set with $n=|P|$ elements and let $m$ be a natural number. If
--   $$3\le n\le 3m,$$
--   then $P$ can be partitioned into three nonempty, pairwise disjoint sets $A$, $B$, $C$ with $A\cup B\cup C = P$, each of which has at most $m$ members.
--
--   This is the first step of the impossibility proof: each of $A\cup C$, $B\cup C$, $A\cup B$ then has at least $n-m$ members, so each may serve as the set of nonfaulty processors.
--
--   **Formalization Note** The page writes "Since $n\le 3m$"; the hypothesis $n\ge 3$ needed for three nonempty parts is implicit there and is stated explicitly here.
-- source:
--   Pease, Shostak & Lamport, Reaching agreement in the presence of faults, J. ACM 27 (1980), p. 232, Section 4, proof of the THEOREM, first paragraph

import Mathlib

namespace InteractiveConsistency.Impossibility

/-- Pease, Shostak & Lamport (1980), Section 4, proof of the THEOREM, p. 232: since `3 ≤ n ≤ 3m`
(`n = |P|`), `P` can be partitioned into three nonempty sets `A`, `B`, `C`, each of which has no
more than `m` members. -/
theorem partition_of_le_three_mul {α : Type*} [DecidableEq α] (P : Finset α) (m : ℕ)
    (h3 : 3 ≤ P.card) (hn : P.card ≤ 3 * m) :
    ∃ A B C : Finset α,
      A.Nonempty ∧ B.Nonempty ∧ C.Nonempty ∧
      Disjoint A B ∧ Disjoint A C ∧ Disjoint B C ∧
      A ∪ B ∪ C = P ∧
      A.card ≤ m ∧ B.card ≤ m ∧ C.card ≤ m := by sorry

end InteractiveConsistency.Impossibility
