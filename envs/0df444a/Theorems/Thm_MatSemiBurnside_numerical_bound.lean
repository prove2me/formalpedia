-- Prove2me | Theorems.Thm_MatSemiBurnside_numerical_bound
-- name    : MatSemiBurnside.numerical_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:38:20.514487+00:00
-- url     : https://prove2.me/theorems/ae03615f-4eea-4d71-bc3d-c7f4de9f95a8
-- title:
--   Numerical bound: $M_d\le N$ and (10) give $M_1+1\le F_d(N,m)$
-- statement:
--   Let $d,m,N$ be positive integers and $h=2^{d+2}$. Let $M_1,\dots,M_d$ be natural numbers with $M_d\le N$ and, for $1\le r<d$,
--   $$M_r\le M_{r+1}+(M_{r+1}+1)\big(1+t_r+Nt_r^2\big)^h,\qquad t_r=m(M_{r+1}+1).$$
--   Then
--   $$M_1+1\le\big[m(N+1)^2\big]^{(2^{d+3}+1)^{d-1}}=F_d(N,m).$$
--
--   This is the arithmetic that turns the recurrence (10) into the bound $|\langle X\rangle/\sim|\le M_1+1\le F_d(N,|X|)$ of Theorem 1; for $d=1$ it reads $M_1+1\le N+1\le m(N+1)^2$.
--
--   Differences from the source:
--   - generalization: the numbers M_r of the proof (K_r = M_r + 1), with K_d ≤ N + 1 and (10) → any natural numbers `M r` with `M d ≤ N` and the recurrence (10) for 1 ≤ r < d; reason: the paragraph uses only these facts about the M_r, so the statement specializes to the proof's numbers
-- source:
--   Guttenberg, Lhote, Shirmohammadi, Worrell, Burnside Problems for Matrix Semigroup Quotients with Applications to Border Complexity, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.31

import Mathlib
import Definitions.Def_MatSemiBurnside_F
set_option autoImplicit false

namespace MatSemiBurnside

/-- **The numerical bound.** Guttenberg, Lhote, Shirmohammadi, Worrell, *Burnside Problems for Matrix Semigroup Quotients
with Applications to Border Complexity*, STOC 2027 submission (held version, sha256 1bc61d4e…), Appendix B, proof of Theorem 1, p.31: "We now verify the stated
numerical bound. Put Kr = Mr + 1 and A = (N + 3)m². [...] Iterating d − 1 times and using Kd ≤ N + 1
gives |⟨X⟩/∼| ≤ K1 ≤ [√A (N + 1)]^((2h+1)^(d−1)) ≤ [m(N + 1)²]^((2^(d+3)+1)^(d−1)) = Fd(N, m), where
the last inequality uses √(N + 3) ≤ N + 1 for N ≥ 1. This also covers the case d = 1, when no
induction step is needed."

The arithmetic part of the argument: natural numbers M_1, …, M_d with M_d ≤ N that satisfy the
recurrence (10) for 1 ≤ r < d have K_1 = M_1 + 1 ≤ F_d(N, m).

**Formalization Note.** `M : ℕ → ℕ` is read only at 1 ≤ r ≤ d. h = 2^(d+2), t = m(M_{r+1} + 1). -/
theorem numerical_bound (d m N : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) (hN : 1 ≤ N) (M : ℕ → ℕ)
    (hMd : M d ≤ N)
    (hrec : ∀ r, 1 ≤ r → r < d →
      M r ≤ M (r + 1) + (M (r + 1) + 1) *
        (1 + m * (M (r + 1) + 1) + N * (m * (M (r + 1) + 1)) ^ 2) ^ (2 ^ (d + 2))) :
    M 1 + 1 ≤ F d N m := by sorry

end MatSemiBurnside
