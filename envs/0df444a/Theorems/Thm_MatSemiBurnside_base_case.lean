-- Prove2me | Theorems.Thm_MatSemiBurnside_base_case
-- name    : MatSemiBurnside.base_case
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:35.82818+00:00
-- url     : https://prove2.me/theorems/206cbe13-5700-45d9-9cbd-8a8611f64d64
-- title:
--   Base case: invertibles form a stable subsemigroup and $M_d\le N$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite and nonempty, $\sim$ a congruence on $\langle X\rangle$ and $N\ge1$ such that every stable subsemigroup $S\le\langle X\rangle$ satisfies $|S/\sim|\le N$. Then
--
--   1. the invertible matrices in $\langle X\rangle$ are closed under multiplication and form a stable set;
--   2. the number $M_d$ of classes $c$ of $\langle X\rangle/\sim$ with $\rho(c)\ge d$ satisfies
--   $$M_d\le N.$$
--
--   This is the base case of the decreasing induction on the minimum rank in the proof of Theorem 1.
--
--   **Formalization Note** $M_d$ is a `Set.encard`. Since every rank is at most $d$, the classes with $\rho\ge d$ are exactly those of minimum rank $d$.
--
--   Differences from the source:
--   - encoding: M_d, the number of classes c with ρ(c) ≥ d → `{q | d ≤ minRank c q}.encard`; reason: the same count, in ℕ ∪ {∞}
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.30

import Mathlib
import Definitions.Def_MatSemiBurnside_classesMeeting
import Definitions.Def_MatSemiBurnside_minRank
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Base case: M_d ≤ N.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.30: "For the base case, the
invertible matrices in ⟨X⟩ form a stable subsemigroup, if there are any. Every class with minimum
rank d meets this subsemigroup, so Md ≤ N." Here M_r is "the number of classes c with ρ(c) ≥ r".

**Formalization Note.** Two conclusions: the set of invertible elements of ⟨X⟩ is closed under
products and is a stable set; and the number of classes q of ⟨X⟩/∼ with `d ≤ minRank c q`,
counted by `Set.encard`, is at most N. -/
theorem base_case {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (hX : X.Nonempty)
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (N : ℕ) (hN : 1 ≤ N) (hbound : UniformStableBound X c N) :
    (∀ a ∈ {a : Matrix (Fin d) (Fin d) ℚ | a ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) ∧ IsUnit a}, ∀ b ∈ {a : Matrix (Fin d) (Fin d) ℚ | a ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) ∧ IsUnit a},
        a * b ∈ {a : Matrix (Fin d) (Fin d) ℚ | a ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) ∧ IsUnit a}) ∧
      IsStableSet {a : Matrix (Fin d) (Fin d) ℚ | a ∈ Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)) ∧ IsUnit a} ∧
      {q : c.Quotient | d ≤ minRank c q}.encard ≤ (N : ℕ∞) := by sorry

end MatSemiBurnside
