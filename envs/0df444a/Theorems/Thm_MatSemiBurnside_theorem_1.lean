-- Prove2me | Theorems.Thm_MatSemiBurnside_theorem_1
-- name    : MatSemiBurnside.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:12.140271+00:00
-- url     : https://prove2.me/theorems/6272b6ef-b90e-4be6-84eb-ba5fb6274add
-- title:
--   Theorem 1: $\langle X\rangle/\sim$ is finite iff stable subsemigroups meet $\le N$ classes; size and diameter $\le F_d(N,|X|)$
-- statement:
--   Let $d$ be a positive integer, let $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ be finite, and let $\sim$ be a congruence on the semigroup $\langle X\rangle$ of all nonempty products of matrices from $X$. Write
--   $$F_d(N,m)=\big[m(N+1)^2\big]^{(2^{d+3}+1)^{d-1}}.$$
--
--   1. $\langle X\rangle/\sim$ is finite if and only if there is an $N\ge1$ such that $|S/\sim|\le N$ for every stable subsemigroup $S\le\langle X\rangle$.
--   2. For every $N\ge1$ such that $|S/\sim|\le N$ for every stable subsemigroup $S\le\langle X\rangle$, the quotient $\langle X\rangle/\sim$ is finite,
--   $$|\langle X\rangle/\sim|\le F_d(N,|X|),$$
--   and its diameter is at most $F_d(N,|X|)$: every $a\in\langle X\rangle$ is congruent to a product $a_1\cdots a_k$ of elements of $X$ with $1\le k\le F_d(N,|X|)$.
--
--   Here a subsemigroup is stable when all its elements have the same rank as each other and as their pairwise products, the same kernel and the same image (row action), and $|S/\sim|$ is the number of classes of $\langle X\rangle/\sim$ that meet $S$. The quotient need not embed in any matrix monoid, so the McNaughton–Zalcstein theorem does not apply to it.
--
--   **Formalization Note** $X$ is a `Finset`, $|X|$ its cardinality, $\langle X\rangle$ is `Subsemigroup.closure X` and $\sim$ any `Con` on it. $|S/\sim|$ is a `Set.encard` in $\mathbb N\cup\{\infty\}$. The cardinality bound is stated together with finiteness, so that `Nat.card` is the true cardinality.
--
--   Differences from the source:
--   - generalization: X finite and nonempty (standing assumption of §3, p.7: "fix a finite nonempty set X") → any finite X, the empty set included; reason: for X = ∅, ⟨X⟩ and the quotient are empty, every stable S ≤ ⟨X⟩ is empty, N = 1 works, the cardinality is 0 = F_d(N, 0) and the diameter clause is vacuous; the statement specializes to nonempty X
--   - reading: "The cardinality and the diameter of the quotient are at most F_d(N, |X|)" → for every N ≥ 1 with the uniform bound: finite, `Nat.card` ≤ F_d(N, |X|) and diameter ≤ F_d(N, |X|); reason: N is the N of the preceding sentence, and the proof (Appendix B, p.30) derives the bound for an arbitrary such N; the existential reading is weaker
--   - encoding: |S/∼|; "the diameter is at most F" → `Set.encard` of the classes met by S; every element of ⟨X⟩ is congruent to a word of length between 1 and F (`DiameterLE`); reason: the same values: the diameter is the least bound on the lengths of the classes
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 1, p.3 (restated identically pp.7 and 30; F_d from eq. (1), p.7)

import Mathlib
import Definitions.Def_MatSemiBurnside_classesMeeting
import Definitions.Def_MatSemiBurnside_IsProdRepr
import Definitions.Def_MatSemiBurnside_F
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Theorem 1.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 1, p.3 (restated identically pp.7 and 30): "Let X ⊆ Matd(ℚ) be
finite, and ∼ be a congruence on ⟨X⟩. Then ⟨X⟩/∼ is finite if and only if there is an N ≥ 1 such
that |S/∼| ≤ N for every stable subsemigroup S ≤ ⟨X⟩. The cardinality and the diameter of the
quotient are at most Fd(N, |X|)." with Fd(N, m) := [m(N + 1)²]^((2^(d+3)+1)^(d−1)) (eq. (1), p.7).

**Formalization Note.**
* d is a positive integer; X is a `Finset` (possibly empty), |X| = `X.card`; ⟨X⟩ is
  `Subsemigroup.closure X` and ∼ is any congruence `c` on it.
* |S/∼| is the `Set.encard` of the set of classes met by S (`UniformStableBound`).
* The bound clause holds for **every** N ≥ 1 with the uniform bound: for each such N the quotient is
  finite, its cardinality (`Nat.card`) is at most F_d(N, |X|), and its diameter is at most
  F_d(N, |X|) (every element of ⟨X⟩ is congruent to a product of between 1 and F_d(N, |X|)
  elements of X, `DiameterLE`). -/
theorem theorem_1 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) :
    (Finite c.Quotient ↔ ∃ N : ℕ, 1 ≤ N ∧ UniformStableBound X c N) ∧
    ∀ N : ℕ, 1 ≤ N → UniformStableBound X c N →
      Finite c.Quotient ∧ Nat.card c.Quotient ≤ F d N X.card ∧ DiameterLE X c (F d N X.card) := by sorry

end MatSemiBurnside
