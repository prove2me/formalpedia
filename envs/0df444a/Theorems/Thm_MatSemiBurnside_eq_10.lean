-- Prove2me | Theorems.Thm_MatSemiBurnside_eq_10
-- name    : MatSemiBurnside.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:40:16.577268+00:00
-- url     : https://prove2.me/theorems/4e44f65a-272e-4b56-853b-6c0a48e9ae10
-- title:
--   Recurrence (10): $M_r\le n+(n+1)(1+t+Nt^2)^h$
-- statement:
--   Let $d$ be a positive integer, $X\subseteq\mathrm{Mat}_d(\mathbb Q)$ finite and nonempty with $m=|X|$, $\sim$ a congruence on $\langle X\rangle$ and $N\ge1$ such that every stable subsemigroup $S\le\langle X\rangle$ satisfies $|S/\sim|\le N$. Write $h=2^{d+2}$ and let $M_r$ be the number of classes $c$ with $\rho(c)\ge r$. If $1\le r<d$ and $M_{r+1}=n$ is finite, then $M_r$ is finite and
--   $$M_r\le n+(n+1)(1+t+Nt^2)^h,\qquad t=m(n+1).$$
--
--   This is the induction step of the proof of Theorem 1.
--
--   **Formalization Note** $M_r$ is a `Set.encard` in $\mathbb N\cup\{\infty\}$; the conclusion bounds it by a natural number and so asserts its finiteness.
--
--   Differences from the source:
--   - encoding: M_r, the number of classes c with ρ(c) ≥ r → `{q | r ≤ minRank c q}.encard`; reason: the same count, in ℕ ∪ {∞}
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (10), p.31 (with the definitions of p.30)

import Mathlib
import Definitions.Def_MatSemiBurnside_classesMeeting
import Definitions.Def_MatSemiBurnside_minRank
set_option autoImplicit false

namespace MatSemiBurnside

/-- **Recurrence (10).** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, eq. (10), p.31, under the standing
bound N on stable subsemigroups: "Suppose that r < d and that Mr+1 = n is finite. [...]
Consequently, Mr ≤ n + (n + 1)(1 + t + Nt²)^h, n = Mr+1, t = m(n + 1). (10)" with m = |X|,
h = 2^(d+2) and M_r "the number of classes c with ρ(c) ≥ r" (p.30), for 1 ≤ r ≤ d.

**Formalization Note.** M_r is `{q | r ≤ minRank c q}.encard` in ℕ ∪ {∞}. The hypothesis M_{r+1} = n
is the finiteness of M_{r+1}; the conclusion bounds M_r by a natural number, so it also asserts
that M_r is finite ("these numbers are finite and satisfy an explicit recurrence", p.30). -/
theorem eq_10 {d : ℕ} (hd : 0 < d) (X : Finset (Matrix (Fin d) (Fin d) ℚ)) (hX : X.Nonempty)
    (c : Con (Subsemigroup.closure (X : Set (Matrix (Fin d) (Fin d) ℚ)))) (N : ℕ) (hN : 1 ≤ N) (hbound : UniformStableBound X c N)
    (r n : ℕ) (hr1 : 1 ≤ r) (hrd : r < d)
    (hn : {q : c.Quotient | r + 1 ≤ minRank c q}.encard = (n : ℕ∞)) :
    {q : c.Quotient | r ≤ minRank c q}.encard ≤
      ((n + (n + 1) * (1 + X.card * (n + 1) + N * (X.card * (n + 1)) ^ 2) ^ (2 ^ (d + 2)) : ℕ) :
        ℕ∞) := by sorry

end MatSemiBurnside
