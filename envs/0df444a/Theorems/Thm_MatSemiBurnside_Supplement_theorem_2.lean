-- Prove2me | Theorems.Thm_MatSemiBurnside_Supplement_theorem_2
-- name    : MatSemiBurnside.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:46:29.831473+00:00
-- url     : https://prove2.me/theorems/08a15cdc-08fc-4098-bbb9-bb5dcfb83857
-- title:
--   Theorem 2: $\langle X\rangle/\sim$ is finite iff rank-stable subsemigroups meet $\le N$ classes; diameter $\le G_d(N)$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite, and $\sim$ a congruence on the semigroup $\langle X\rangle$ of all nonempty products of matrices from $X$. Let
--   $$G_d(N)=(N+1)(H+1)^d-1,\qquad H=\binom{N+D^2+1}{D^2},\qquad D=\binom{d}{\lfloor d/2\rfloor}.$$
--
--   1. $\langle X\rangle/\sim$ is finite if and only if there is an $N\ge1$ such that $|S/\sim|\le N$ for every rank-stable subsemigroup $S\le\langle X\rangle$.
--   2. For every such $N$, the diameter of $\langle X\rangle/\sim$ is at most $G_d(N)$: every $a\in\langle X\rangle$ satisfies $a\sim a_1\cdots a_k$ with $a_1,\dots,a_k\in X$ and $1\le k\le G_d(N)$.
--
--   Here $|S/\sim|$ is the number of classes of $\langle X\rangle/\sim$ that meet $S$. Compared with Theorem 1, the hypothesis covers all rank-stable subsemigroups rather than only stable ones, and in return the diameter bound is doubly exponential only in $d$ and independent of $|X|$.
--
--   **Formalization Note** $X$ is a `Finset`, $\langle X\rangle$ is `Subsemigroup.closure X`, and the diameter clause uses the base definition `DiameterLE`.
--
--   Differences from the source:
--   - generalization: X finite and nonempty (standing assumption of §3, p.7, and of Appendix D, p.33) → any finite X, the empty set included; reason: for X = ∅ the quotient is empty and finite, every rank-stable S ≤ ⟨X⟩ is empty so N = 1 works, and the diameter clause is vacuous; the statement specializes to nonempty X
--   - reading: "The diameter of the quotient is at most G_d(N)" → for every N ≥ 1 with the uniform bound; reason: N is the N of the preceding sentence, and Appendix D (p.33) proves the bound for an arbitrary such N; the existential reading is weaker
--   - encoding: |S/∼|; "the diameter is at most G_d(N)" → `Set.encard` of the classes met by S; every element of ⟨X⟩ is congruent to a word over X of length between 1 and G_d(N) (`DiameterLE`); reason: the same values, the diameter is the least bound on the lengths of the classes
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 2, p.4 (restated identically pp.10 and 35; G_d from eq. (2), p.10; proof Appendix D, pp.33–35)

import Mathlib
import Definitions.Def_MatSemiBurnside_IsProdRepr
import Definitions.Def_MatSemiBurnside_Supplement_G
import Definitions.Def_MatSemiBurnside_Supplement_UniformRankStableBound
set_option autoImplicit false

namespace MatSemiBurnside.Supplement

open MatSemiBurnside

/-- **Theorem 2.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Theorem 2, p.4 (restated identically pp.10 and 35; proof App. D, pp.33–35):
"Let X ⊆ Mat_d(ℚ) be finite and ∼ be a congruence on ⟨X⟩. Then ⟨X⟩/∼ is finite if and only if there is an
N ≥ 1 such that |S/∼| ≤ N for every rank-stable subsemigroup S ≤ ⟨X⟩. The diameter of the quotient is at most
G_d(N)." with G_d(N) = (N + 1)(H + 1)^d − 1 (eq. (2), p.10).

**Formalization Note.**
* d is a positive integer; X is a `Finset` (possibly empty); ⟨X⟩ is `Subsemigroup.closure X` and ∼ any
  congruence `c` on it.
* |S/∼| is the `Set.encard` of the classes met by S (`UniformRankStableBound`).
* The diameter clause holds for **every** N ≥ 1 with the uniform bound: every element of ⟨X⟩ is congruent to a
  product of between 1 and G_d(N) elements of X (base `DiameterLE`). -/
theorem theorem_2 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) :
    (Finite c.Quotient ↔ ∃ N : ℕ, 1 ≤ N ∧ UniformRankStableBound X c N) ∧
    ∀ N : ℕ, 1 ≤ N → UniformRankStableBound X c N → DiameterLE X c (G d N) := by sorry

end MatSemiBurnside.Supplement
